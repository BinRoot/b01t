"""Build context, DSLFunction, @parametric/@adaptive decorators, adjoint."""

from contextlib import contextmanager
from dataclasses import dataclass, field
from typing import Any, Callable, Optional, Sequence

from .types import (
    DSLValidationError, Effect, GateOp, IRProgram, Op, QReg,
    AncillaBlockOp, MeasureOp, MeasureAllOp, IfOp, ParOp,
)
from .gates import _ALLOWED_COMPUTE, _ALLOWED_PHASE, _inverse_ops
from .safety import is_safe_program


# ---------------------------------------------------------------------------
# Internal capture state
# ---------------------------------------------------------------------------

@dataclass
class _AncillaCapture:
    reg: QReg
    compute_ops: list[GateOp] = field(default_factory=list)
    phase_ops: list[GateOp] = field(default_factory=list)
    has_compute: bool = False
    has_phase: bool = False
    has_uncompute: bool = False
    completed_stages: list[tuple[list[GateOp], list[GateOp], list[GateOp]]] = field(default_factory=list)


@dataclass
class _BuildContext:
    fn_name: str
    effect: Effect
    regs: list[QReg]
    ops: list[Op] = field(default_factory=list)
    ancilla: Optional[_AncillaCapture] = None
    mode: Optional[str] = None


_CTX_STACK: list[_BuildContext] = []


def _validate_build_register_names(regs: list[QReg]) -> None:
    """Reject duplicate register names."""
    seen: set[str] = set()
    for r in regs:
        if r.name in seen:
            raise DSLValidationError(f"duplicate register name '{r.name}'")
        seen.add(r.name)


def _fresh_anc_name_broad(ctx: _BuildContext) -> str:
    """Generate an ancilla name that doesn't collide with existing registers."""
    existing = {r.name for r in ctx.regs}
    idx = len([r for r in ctx.regs if r.kind == "anc"])
    name = f"anc{idx}"
    while name in existing:
        idx += 1
        name = f"anc{idx}"
    return name


@contextmanager
def _push_ctx(ctx: _BuildContext):
    _CTX_STACK.append(ctx)
    try:
        yield ctx
    finally:
        popped = _CTX_STACK.pop()
        if popped is not ctx:
            raise RuntimeError("internal build-context stack corruption")


def _ctx() -> _BuildContext:
    if not _CTX_STACK:
        raise DSLValidationError("No active DSL build context. Use decorated_fn.build(...).")
    return _CTX_STACK[-1]


def _capture_ops(fn: Callable[[], Any]) -> list[Op]:
    parent = _ctx()
    nested = _BuildContext(fn_name=f"<capture:{parent.fn_name}>", effect=parent.effect, regs=parent.regs)
    with _push_ctx(nested):
        fn()
    if nested.ancilla is not None:
        raise DSLValidationError("ancilla blocks are not supported inside captured control-flow bodies")
    return nested.ops


def _append_op(op: Op) -> None:
    ctx = _ctx()
    anc = ctx.ancilla
    if anc is not None:
        if ctx.mode == "compute":
            if not isinstance(op, GateOp):
                raise DSLValidationError("compute blocks may only contain reversible gates")
            if op.name not in _ALLOWED_COMPUTE:
                raise DSLValidationError(f"gate '{op.name}' is not allowed in compute blocks")
            anc.compute_ops.append(op)
            return
        if ctx.mode == "phase":
            if not isinstance(op, GateOp):
                raise DSLValidationError("phase blocks may only contain diagonal gates")
            if op.name not in _ALLOWED_PHASE:
                raise DSLValidationError(f"gate '{op.name}' is not allowed in phase blocks")
            anc.phase_ops.append(op)
            return
        raise DSLValidationError("inside an ancilla block, use compute(...), phase(...), and uncompute()")
    ctx.ops.append(op)


# ---------------------------------------------------------------------------
# DSLFunction
# ---------------------------------------------------------------------------

class DSLFunction:
    def __init__(self, fn: Callable[..., Any], effect: Effect):
        self.fn = fn
        self.effect = effect
        self.__name__ = fn.__name__
        self.__doc__ = fn.__doc__

    def __call__(self, *args, **kwargs):
        if kwargs:
            raise DSLValidationError("keyword arguments are not supported in the MVP")
        if not _CTX_STACK:
            raise DSLValidationError(f"{self.__name__} is a DSL function; use {self.__name__}.build(...) to produce IR")
        caller = _ctx()
        if caller.effect is Effect.COHERENT and self.effect is Effect.ADAPTIVE:
            raise DSLValidationError("coherent functions cannot call adaptive functions")
        return self.fn(*args)

    def build(self, *arg_specs: tuple[str, int]) -> IRProgram:
        regs: list[QReg] = []
        for spec in arg_specs:
            if isinstance(spec, QReg):
                regs.append(spec)
            else:
                if not (isinstance(spec, tuple) and len(spec) == 2):
                    raise DSLValidationError("build(...) expects specs like ('sys', 3)")
                name, size = spec
                regs.append(QReg(name=name, size=size, kind="sys"))
        _validate_build_register_names(regs)
        ctx = _BuildContext(fn_name=self.__name__, effect=self.effect, regs=regs)
        with _push_ctx(ctx):
            self.fn(*regs)
        return IRProgram(
            name=self.__name__, effect=self.effect, regs=regs,
            ops=ctx.ops, is_safe=is_safe_program(self.effect, ctx.ops),
        )


def parametric(fn: Callable[..., Any]) -> DSLFunction:
    """Decorator: parametric coherent program (allows arbitrary-angle rotations)."""
    return DSLFunction(fn, Effect.COHERENT)


def adaptive(fn: Callable[..., Any]) -> DSLFunction:
    return DSLFunction(fn, Effect.ADAPTIVE)


def adjoint(fn: DSLFunction, *args) -> None:
    """Emit the inverse of a coherent subroutine into the current context."""
    if not isinstance(fn, DSLFunction):
        raise DSLValidationError("adjoint() requires a DSLFunction")
    if fn.effect is not Effect.COHERENT:
        raise DSLValidationError("adjoint() only works on coherent functions")
    caller = _ctx()
    if caller.ancilla is not None:
        raise DSLValidationError("adjoint() cannot be used inside an ancilla compute/phase/uncompute block")
    sub_ctx = _BuildContext(fn_name=f"<adjoint:{fn.__name__}>", effect=Effect.COHERENT, regs=caller.regs)
    with _push_ctx(sub_ctx):
        fn.fn(*args)
    inv_ops = _inverse_ops(sub_ctx.ops)
    for op in inv_ops:
        _append_op(op)
