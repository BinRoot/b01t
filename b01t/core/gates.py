"""Gate definitions, allowlists, and inverse rules."""

from typing import Any, Sequence

from .types import DSLValidationError, Effect, GateOp, Wire, AncillaBlockOp, ParOp, Op


# ---------------------------------------------------------------------------
# Allowlists and inverse rules
# ---------------------------------------------------------------------------

_ALLOWED_COMPUTE = {"x", "cx", "ccx", "swap", "mcx"}
_ALLOWED_PHASE = {"z", "rz", "cz", "ccz", "s", "sdg", "t", "tdg", "mcz"}
_SELF_INVERSE = {"x", "h", "z", "cx", "ccx", "cz", "ccz", "swap", "mcx", "mcz"}
_INVERSE_PAIRS = {"s": "sdg", "sdg": "s", "t": "tdg", "tdg": "t"}

# Exact-safe gate set for top-level ops in the safe fragment.
# These are gates synthesisable exactly from {H, S, T, CNOT}.
# Note: rz is in _ALLOWED_PHASE (used inside ancilla blocks with specific
# angles) but is NOT exact-safe at top level because it takes an arbitrary
# parameter. h is exact-safe but not in compute or phase allowlists.
_ALLOWED_SAFE_GATES = (_ALLOWED_COMPUTE | _ALLOWED_PHASE | {"h"}) - {"rz"}


def _inverse_gate(op: GateOp) -> GateOp:
    if op.name in _SELF_INVERSE:
        return GateOp(op.name, op.wires, op.params)
    if op.name in _INVERSE_PAIRS:
        return GateOp(_INVERSE_PAIRS[op.name], op.wires, op.params)
    if op.name in ("rz", "ry", "rx"):
        if len(op.params) != 1:
            raise DSLValidationError(f"{op.name} inverse expects exactly one angle")
        return GateOp(op.name, op.wires, (-op.params[0],))
    if op.name in ("cry", "crz", "crx"):
        if len(op.params) != 1:
            raise DSLValidationError(f"{op.name} inverse expects exactly one angle")
        return GateOp(op.name, op.wires, (-op.params[0],))
    raise DSLValidationError(f"no inverse rule available for gate '{op.name}'")


def _inverse_ops(ops: Sequence[Op]) -> list[Op]:
    """Reverse a list of ops and invert each gate."""
    result: list[Op] = []
    for op in reversed(ops):
        if isinstance(op, GateOp):
            result.append(_inverse_gate(op))
        elif isinstance(op, AncillaBlockOp):
            result.append(AncillaBlockOp(
                ancilla=op.ancilla,
                compute_ops=[_inverse_gate(g) for g in reversed(op.uncompute_ops)],
                phase_ops=[_inverse_gate(g) for g in reversed(op.phase_ops)],
                uncompute_ops=[_inverse_gate(g) for g in reversed(op.compute_ops)],
            ))
        elif isinstance(op, ParOp):
            result.append(ParOp(
                left_ops=_inverse_ops(op.left_ops),
                right_ops=_inverse_ops(op.right_ops),
            ))
        else:
            raise DSLValidationError(f"adjoint does not support {type(op).__name__}")
    return result


def _validate_no_dirty_swap(ops: Sequence[GateOp]) -> None:
    for i in range(len(ops) - 2):
        a, b, c = ops[i : i + 3]
        if a.name == b.name == c.name == "cx":
            if len(a.wires) == len(b.wires) == len(c.wires) == 2:
                if a.wires == c.wires and b.wires == (a.wires[1], a.wires[0]):
                    raise DSLValidationError(
                        "dirty-swap style compute pattern detected; swap-like rewrites are rejected in the MVP"
                    )


# ---------------------------------------------------------------------------
# Wire validation + gate emission helper
# ---------------------------------------------------------------------------

def _wire_args(*wires: Wire) -> tuple[Wire, ...]:
    for wire in wires:
        if not isinstance(wire, Wire):
            raise DSLValidationError(f"expected a Wire argument, got {type(wire).__name__}")
    if len(wires) > 1 and len(set(wires)) != len(wires):
        raise DSLValidationError("multi-qubit gate requires distinct wires")
    return tuple(wires)


def _validate_wires_declared(wires: tuple[Wire, ...], regs: list) -> None:
    """Check that every wire references a declared register and is in bounds."""
    reg_map = {r.name: r for r in regs}
    for w in wires:
        if w.reg not in reg_map:
            raise DSLValidationError(f"wire references undeclared register '{w.reg}'")
        reg = reg_map[w.reg]
        if w.index < 0 or w.index >= reg.size:
            raise DSLValidationError(
                f"wire index {w.index} out of range for register "
                f"'{w.reg}' (size {reg.size})")


def _gate(name: str, *wires: Wire, params: tuple[Any, ...] = ()) -> None:
    # If inside an exact build context, route there instead
    from .exact_builder import _try_exact_append
    validated = _wire_args(*wires)
    if _try_exact_append(name, validated, params):
        return
    # Broad IR path
    from .builder import _ctx, _append_op
    ctx = _ctx()
    _validate_wires_declared(validated, ctx.regs)
    _append_op(GateOp(name=name, wires=validated, params=params))


# ---------------------------------------------------------------------------
# Gate functions
# ---------------------------------------------------------------------------

# Single-qubit
def x(q: Wire) -> None: _gate("x", q)
def h(q: Wire) -> None: _gate("h", q)
def z(q: Wire) -> None: _gate("z", q)
def s(q: Wire) -> None: _gate("s", q)
def sdg(q: Wire) -> None: _gate("sdg", q)
def t(q: Wire) -> None: _gate("t", q)
def tdg(q: Wire) -> None: _gate("tdg", q)
def ry(theta: float, q: Wire) -> None: _gate("ry", q, params=(theta,))
def rx(theta: float, q: Wire) -> None: _gate("rx", q, params=(theta,))
def rz(theta: float, q: Wire) -> None: _gate("rz", q, params=(theta,))

# Two-qubit
def cx(control: Wire, target: Wire) -> None: _gate("cx", control, target)
def cz(control: Wire, target: Wire) -> None: _gate("cz", control, target)
def swap(a: Wire, b: Wire) -> None: _gate("swap", a, b)
def cry(theta: float, control: Wire, target: Wire) -> None: _gate("cry", control, target, params=(theta,))
def crz(theta: float, control: Wire, target: Wire) -> None: _gate("crz", control, target, params=(theta,))

# Three-qubit
def ccx(c0: Wire, c1: Wire, target: Wire) -> None: _gate("ccx", c0, c1, target)
def ccz(c0: Wire, c1: Wire, target: Wire) -> None: _gate("ccz", c0, c1, target)

# Multi-controlled
def mcx(controls: Sequence[Wire], target: Wire) -> None:
    if len(controls) < 1:
        raise DSLValidationError("mcx requires at least one control wire")
    _gate("mcx", *controls, target)

def mcz(controls: Sequence[Wire], target: Wire) -> None:
    if len(controls) < 1:
        raise DSLValidationError("mcz requires at least one control wire")
    _gate("mcz", *controls, target)


# Measurement (adaptive only)
def measure(q: Wire) -> str:
    from .exact_builder import _try_exact_reject_measure
    _try_exact_reject_measure()
    if not isinstance(q, Wire):
        raise DSLValidationError(f"expected a Wire argument, got {type(q).__name__}")
    from .builder import _ctx, _append_op
    from .types import MeasureOp
    ctx = _ctx()
    if ctx.effect is Effect.COHERENT:
        raise DSLValidationError("coherent functions cannot measure")
    _validate_wires_declared((q,), ctx.regs)
    _append_op(MeasureOp(q))
    return f"m_{q.reg}_{q.index}"


def measure_all(reg) -> list[str]:
    from .exact_builder import _try_exact_reject_measure
    _try_exact_reject_measure()
    from .builder import _ctx, _append_op
    from .types import MeasureAllOp
    ctx = _ctx()
    if ctx.effect is Effect.COHERENT:
        raise DSLValidationError("coherent functions cannot measure")
    reg_map = {r.name: r for r in ctx.regs}
    if reg.name not in reg_map:
        raise DSLValidationError(f"measure_all references undeclared register '{reg.name}'")
    _append_op(MeasureAllOp(reg.name, reg.size))
    return [f"m_{reg.name}_{i}" for i in range(reg.size)]
