"""Control flow: repeat, for_each, par, if_then."""

from typing import Any, Callable, Optional, Sequence

from b01t.core.types import DSLValidationError, Effect, GateOp, IfOp, ParOp
from b01t.core.builder import _ctx, _capture_ops, _append_op


def repeat(count: int, body: Callable[[], Any]) -> None:
    for _ in range(count):
        body()


def for_each(data: Sequence[Any], body: Callable[[int, Any], Any]) -> None:
    """Iterate classical data at build time, emitting parameterised gates."""
    for i, val in enumerate(data):
        body(i, val)


def _collect_wires(ops) -> set:
    """Collect all wires referenced in a list of ops."""
    wires = set()
    for op in ops:
        if isinstance(op, GateOp):
            wires.update(op.wires)
        elif isinstance(op, ParOp):
            wires.update(_collect_wires(op.left_ops))
            wires.update(_collect_wires(op.right_ops))
    return wires


def par(fn1: Callable[[], Any], fn2: Callable[[], Any]) -> None:
    """Parallel (tensor) composition: fn1 and fn2 operate on disjoint registers."""
    left = _capture_ops(fn1)
    right = _capture_ops(fn2)
    overlap = _collect_wires(left) & _collect_wires(right)
    if overlap:
        labels = ", ".join(str(w) for w in sorted(overlap, key=str))
        raise DSLValidationError(f"par() requires disjoint wires, overlap on: {labels}")
    _append_op(ParOp(left_ops=left, right_ops=right))


def if_then(cond: Any, then_body: Callable[[], Any], else_body: Optional[Callable[[], Any]] = None) -> None:
    from b01t.core.exact_builder import _try_exact_reject_if_then
    _try_exact_reject_if_then()
    ctx = _ctx()
    if ctx.effect is Effect.COHERENT:
        raise DSLValidationError("coherent functions cannot branch on classical conditions")
    then_ops = _capture_ops(then_body)
    else_ops = _capture_ops(else_body) if else_body is not None else []
    ctx.ops.append(IfOp(cond=cond, then_ops=then_ops, else_ops=else_ops))
