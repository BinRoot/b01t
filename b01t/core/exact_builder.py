"""Exact program builder: @coherent / @primitive and ExactDSLFunction."""

from contextlib import contextmanager
from dataclasses import dataclass, field
from typing import Any, Callable, Optional, Sequence

from .types import DSLValidationError, Wire, QReg, GateOp, MeasureOp, MeasureAllOp, IfOp
from .exact_types import (
    ExactGate, ExactGateOp, ExactAncillaBlock, ExactParOp, ExactOp, ExactProgram,
    Certification, MiddleBlockKind, EXACT_COMPUTE_GATES, EXACT_PHASE_GATES,
)
from .exact_validate import (
    validate_wires_declared, validate_wires_distinct,
    validate_par_disjoint, validate_ancilla_block,
    exact_inverse_gate, exact_inverse_ops, validate_exact_ops,
)


# ---------------------------------------------------------------------------
# Broad gate name -> ExactGate mapping
# ---------------------------------------------------------------------------

_NAME_TO_EXACT: dict[str, ExactGate] = {
    "x": ExactGate.X, "h": ExactGate.H, "z": ExactGate.Z,
    "s": ExactGate.S, "sdg": ExactGate.SDG, "t": ExactGate.T, "tdg": ExactGate.TDG,
    "cx": ExactGate.CX, "cz": ExactGate.CZ, "swap": ExactGate.SWAP,
    "ccx": ExactGate.CCX, "ccz": ExactGate.CCZ,
    "mcx": ExactGate.MCX, "mcz": ExactGate.MCZ,
}

_FORBIDDEN_IN_EXACT = {"rx", "ry", "rz", "cry", "crz", "crx"}


# ---------------------------------------------------------------------------
# Exact build context
# ---------------------------------------------------------------------------

@dataclass
class _ExactAncillaCapture:
    reg: QReg
    compute_ops: list[ExactGateOp] = field(default_factory=list)
    middle_ops: list[ExactGateOp] = field(default_factory=list)
    middle_kind: Optional[MiddleBlockKind] = None
    has_compute: bool = False
    has_middle: bool = False
    has_uncompute: bool = False
    completed_stages: list[tuple[
        list[ExactGateOp], list[ExactGateOp], list[ExactGateOp], MiddleBlockKind
    ]] = field(default_factory=list)


@dataclass
class _ExactBuildContext:
    fn_name: str
    regs: list[QReg]
    ops: list[ExactOp] = field(default_factory=list)
    ancilla: Optional[_ExactAncillaCapture] = None
    mode: Optional[str] = None  # "compute" | "phase" | None
    caller_certification: Optional["Certification"] = None  # set by build_exact


_EXACT_CTX_STACK: list[_ExactBuildContext] = []


def _validate_register_names(regs: list[QReg]) -> None:
    """Reject duplicate register names and names that collide with ancilla naming."""
    seen: set[str] = set()
    for r in regs:
        if r.name in seen:
            raise DSLValidationError(
                f"duplicate register name '{r.name}'")
        seen.add(r.name)


def _fresh_anc_name(ctx: _ExactBuildContext) -> str:
    """Generate an ancilla name that doesn't collide with any existing register."""
    existing = {r.name for r in ctx.regs}
    idx = len([r for r in ctx.regs if r.kind == "anc"])
    name = f"anc{idx}"
    while name in existing:
        idx += 1
        name = f"anc{idx}"
    return name


@contextmanager
def _push_exact_ctx(ctx: _ExactBuildContext):
    _EXACT_CTX_STACK.append(ctx)
    try:
        yield ctx
    finally:
        popped = _EXACT_CTX_STACK.pop()
        if popped is not ctx:
            raise RuntimeError("internal exact build-context stack corruption")


def _exact_ctx() -> Optional[_ExactBuildContext]:
    """Return the current exact build context, or None if not in one."""
    return _EXACT_CTX_STACK[-1] if _EXACT_CTX_STACK else None


def _require_exact_ctx() -> _ExactBuildContext:
    ctx = _exact_ctx()
    if ctx is None:
        raise DSLValidationError("No active exact build context")
    return ctx


# ---------------------------------------------------------------------------
# Gate interception called from the shared gate layer
# ---------------------------------------------------------------------------

def _try_exact_append(gate_name: str, wires: tuple[Wire, ...], params: tuple) -> bool:
    """Try to append a gate to the exact context. Returns True if handled.

    Called by the shared ``_gate()`` helper before falling through to the
    broad-IR path. Returns False when not inside an exact context.
    """
    ctx = _exact_ctx()
    if ctx is None:
        return False

    # Reject parameterized gates
    if gate_name in _FORBIDDEN_IN_EXACT:
        raise DSLValidationError(
            f"gate '{gate_name}' is not allowed in @coherent "
            f"(parameterized rotations are not in the exact gate set)")
    if params:
        raise DSLValidationError(
            f"gate '{gate_name}' with parameters is not allowed in @coherent")

    exact_gate = _NAME_TO_EXACT.get(gate_name)
    if exact_gate is None:
        raise DSLValidationError(
            f"gate '{gate_name}' is not in the exact gate set")

    validate_wires_distinct(wires)
    known_regs = ctx.regs
    if ctx.ancilla is not None:
        known_regs = known_regs + [ctx.ancilla.reg]
    validate_wires_declared(wires, known_regs)

    eop = ExactGateOp(exact_gate, wires)

    anc = ctx.ancilla
    if anc is not None:
        if ctx.mode == "compute":
            if exact_gate not in EXACT_COMPUTE_GATES:
                raise DSLValidationError(
                    f"gate {exact_gate.name} is not allowed in exact compute blocks")
            anc.compute_ops.append(eop)
            return True
        if ctx.mode == "phase":
            if exact_gate not in EXACT_PHASE_GATES:
                raise DSLValidationError(
                    f"gate {exact_gate.name} is not allowed in exact phase blocks")
            anc.middle_ops.append(eop)
            return True
        if ctx.mode == "apply":
            # apply() allows any exact gate (disjointness checked at block finalization)
            anc.middle_ops.append(eop)
            return True
        raise DSLValidationError(
            "inside an ancilla block, use compute(...), phase(...), apply(...), and uncompute()")

    ctx.ops.append(eop)
    return True


def _try_exact_reject_measure() -> bool:
    """Reject measure inside exact context. Returns True if in exact ctx."""
    ctx = _exact_ctx()
    if ctx is None:
        return False
    raise DSLValidationError("measure is not allowed in @coherent")


def _try_exact_reject_if_then() -> bool:
    """Reject if_then inside exact context. Returns True if in exact ctx."""
    ctx = _exact_ctx()
    if ctx is None:
        return False
    raise DSLValidationError("if_then is not allowed in @coherent")


# ---------------------------------------------------------------------------
# Exact capture helpers
# ---------------------------------------------------------------------------

def _exact_capture_ops(fn: Callable[[], Any]) -> list[ExactOp]:
    """Capture exact ops from a lambda in a nested exact context."""
    parent = _require_exact_ctx()
    nested = _ExactBuildContext(
        fn_name=f"<capture:{parent.fn_name}>", regs=parent.regs)
    with _push_exact_ctx(nested):
        fn()
    if nested.ancilla is not None:
        raise DSLValidationError(
            "ancilla blocks are not supported inside captured control-flow bodies")
    return nested.ops


# ---------------------------------------------------------------------------
# Exact ancilla discipline
# ---------------------------------------------------------------------------

class _ExactAncillaManager:
    def __init__(self, size: int):
        self.size = size
        self.reg: Optional[QReg] = None

    def __enter__(self) -> QReg:
        ctx = _require_exact_ctx()
        if ctx.ancilla is not None:
            raise DSLValidationError("nested ancilla blocks are not supported")
        reg = QReg(
            name=_fresh_anc_name(ctx),
            size=self.size, kind="anc")
        ctx.regs.append(reg)
        ctx.ancilla = _ExactAncillaCapture(reg=reg)
        self.reg = reg
        return reg

    def __exit__(self, exc_type, exc, tb) -> None:
        ctx = _require_exact_ctx()
        anc = ctx.ancilla
        try:
            if exc_type is None:
                if anc is None:
                    raise DSLValidationError("internal error: missing ancilla capture")
                if anc.has_compute and not anc.has_uncompute:
                    raise DSLValidationError(
                        "ancilla block exited with incomplete cycle")
                if not anc.completed_stages:
                    raise DSLValidationError(
                        "ancilla block must contain at least one compute/phase/uncompute cycle")
                for compute_ops, middle_ops, uncompute_ops, middle_kind in anc.completed_stages:
                    block = ExactAncillaBlock(
                        ancilla=anc.reg,
                        compute_ops=tuple(compute_ops),
                        middle_ops=tuple(middle_ops),
                        uncompute_ops=tuple(uncompute_ops),
                        middle_kind=middle_kind,
                    )
                    validate_ancilla_block(block)
                    ctx.ops.append(block)
        finally:
            ctx.ancilla = None
            ctx.mode = None


def exact_ancilla(size: int) -> _ExactAncillaManager:
    """Create an exact ancilla block (use inside @coherent)."""
    return _ExactAncillaManager(size)


def exact_compute(fn: Callable[[], Any]) -> None:
    """Exact compute section inside an ancilla block."""
    ctx = _require_exact_ctx()
    if ctx.ancilla is None:
        raise DSLValidationError("compute() must appear inside an ancilla block")
    if ctx.ancilla.has_compute:
        raise DSLValidationError("only one compute() per cycle")
    if ctx.mode is not None:
        raise DSLValidationError("nested compute/phase not supported")
    ctx.mode = "compute"
    try:
        fn()
    finally:
        ctx.mode = None
    ctx.ancilla.has_compute = True


def _exact_middle(fn: Callable[[], Any], kind: MiddleBlockKind, mode_name: str) -> None:
    """Shared logic for phase() and apply() middle sections."""
    ctx = _require_exact_ctx()
    if ctx.ancilla is None:
        raise DSLValidationError(f"{mode_name}() must appear inside an ancilla block")
    if ctx.ancilla.has_middle:
        raise DSLValidationError(f"only one {mode_name}() per cycle")
    if not ctx.ancilla.has_compute:
        raise DSLValidationError(f"{mode_name}() must follow compute()")
    if ctx.mode is not None:
        raise DSLValidationError("nested compute/phase/apply not supported")
    ctx.mode = mode_name
    try:
        fn()
    finally:
        ctx.mode = None
    ctx.ancilla.has_middle = True
    ctx.ancilla.middle_kind = kind


def exact_phase(fn: Callable[[], Any]) -> None:
    """Exact phase section (diagonal gates only, CPU pattern)."""
    _exact_middle(fn, MiddleBlockKind.PHASE, "phase")


def exact_apply(fn: Callable[[], Any]) -> None:
    """Exact apply section (any exact gates on disjoint wires, CMA pattern).

    Gates in the apply block must operate on wires disjoint from the
    compute block's wires. This is the PreservesFirst condition proved
    in ``AncillaApply.lean:cma_ancilla_clean_product``.
    """
    _exact_middle(fn, MiddleBlockKind.APPLY, "apply")


def exact_uncompute() -> None:
    """Auto-generate exact uncompute from compute ops."""
    ctx = _require_exact_ctx()
    if ctx.ancilla is None:
        raise DSLValidationError("uncompute() must appear inside an ancilla block")
    if not ctx.ancilla.has_compute:
        raise DSLValidationError("uncompute() requires a preceding compute()")
    if not ctx.ancilla.has_middle:
        raise DSLValidationError("uncompute() must follow phase() or apply()")
    if ctx.ancilla.has_uncompute:
        raise DSLValidationError("uncompute() must follow a new compute/phase/apply cycle")
    inv = [exact_inverse_gate(g) for g in reversed(ctx.ancilla.compute_ops)]
    ctx.ancilla.completed_stages.append((
        list(ctx.ancilla.compute_ops),
        list(ctx.ancilla.middle_ops),
        inv,
        ctx.ancilla.middle_kind,
    ))
    ctx.ancilla.compute_ops = []
    ctx.ancilla.middle_ops = []
    ctx.ancilla.middle_kind = None
    ctx.ancilla.has_compute = False
    ctx.ancilla.has_middle = False
    ctx.ancilla.has_uncompute = False


# ---------------------------------------------------------------------------
# Exact par
# ---------------------------------------------------------------------------

def exact_par(fn1: Callable[[], Any], fn2: Callable[[], Any]) -> None:
    """Parallel composition with wire-disjointness enforced."""
    left = _exact_capture_ops(fn1)
    right = _exact_capture_ops(fn2)
    validate_par_disjoint(left, right)
    ctx = _require_exact_ctx()
    ctx.ops.append(ExactParOp(left_ops=tuple(left), right_ops=tuple(right)))


# ---------------------------------------------------------------------------
# ExactDSLFunction and @coherent decorator
# ---------------------------------------------------------------------------

class ExactDSLFunction:
    """A DSL function that builds ``ExactProgram`` values."""

    def __init__(self, fn: Callable[..., Any], certification: Certification = Certification.SAFE):
        self.fn = fn
        self.certification = certification
        self.__name__ = fn.__name__
        self.__doc__ = fn.__doc__

    def __call__(self, *args, **kwargs):
        if kwargs:
            raise DSLValidationError("keyword arguments are not supported")
        ctx = _exact_ctx()
        if ctx is not None:
            # If callee is PRIMITIVE and caller is SAFE, and we're not
            # inside an ancilla compute/phase block, reject the call.
            if self.certification == Certification.PRIMITIVE:
                if ctx.ancilla is None or ctx.mode is None:
                    if ctx.caller_certification == Certification.SAFE:
                        raise DSLValidationError(
                            f"@coherent function cannot call @primitive "
                            f"'{self.__name__}' outside an ancilla block. "
                            f"Either wrap the call in compute()/phase(), "
                            f"or declare the caller @primitive.")
            return self.fn(*args)
        raise DSLValidationError(
            f"{self.__name__} is an exact DSL function; "
            f"use {self.__name__}.build_exact(...) to produce an ExactProgram")

    def build_exact(self, *arg_specs: tuple[str, int]) -> ExactProgram:
        """Build an ``ExactProgram`` from register specifications."""
        regs: list[QReg] = []
        for spec in arg_specs:
            if isinstance(spec, QReg):
                regs.append(spec)
            else:
                if not (isinstance(spec, tuple) and len(spec) == 2):
                    raise DSLValidationError(
                        "build_exact() expects specs like ('sys', 3)")
                name, size = spec
                regs.append(QReg(name=name, size=size, kind="sys"))

        _validate_register_names(regs)

        ctx = _ExactBuildContext(
            fn_name=self.__name__, regs=regs,
            caller_certification=self.certification,
        )
        with _push_exact_ctx(ctx):
            self.fn(*regs)

        ops = tuple(ctx.ops)
        all_regs = tuple(ctx.regs)  # includes ancilla regs added during build
        validate_exact_ops(ops, all_regs)
        return ExactProgram(
            name=self.__name__, regs=all_regs, ops=ops,
            certification=self.certification,
        )


def coherent(fn: Callable[..., Any]) -> ExactDSLFunction:
    """Decorator: exact coherent program (IsSafe; closed gate set,
    ancilla-certified, safe by construction)."""
    return ExactDSLFunction(fn, Certification.SAFE)


def primitive(fn: Callable[..., Any]) -> ExactDSLFunction:
    """Decorator: exact primitive program (IsCoh; closed gate set,
    coherent/unitary, but scratch registers are caller-managed)."""
    return ExactDSLFunction(fn, Certification.PRIMITIVE)


def exact_adjoint(fn: ExactDSLFunction, *args) -> None:
    """Emit the inverse of an exact coherent subroutine."""
    if not isinstance(fn, ExactDSLFunction):
        raise DSLValidationError("exact_adjoint() requires an ExactDSLFunction")
    caller = _require_exact_ctx()
    if caller.ancilla is not None:
        raise DSLValidationError(
            "exact_adjoint() cannot be used inside an ancilla block")
    sub_ctx = _ExactBuildContext(
        fn_name=f"<adjoint:{fn.__name__}>", regs=caller.regs)
    with _push_exact_ctx(sub_ctx):
        fn.fn(*args)
    inv_ops = exact_inverse_ops(sub_ctx.ops)
    for op in inv_ops:
        caller.ops.append(op)
