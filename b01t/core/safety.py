"""Safety checker: is_safe_program."""

from typing import Sequence

from .types import (
    Effect, Op, GateOp, AncillaBlockOp, ParOp,
)
from .gates import _ALLOWED_COMPUTE, _ALLOWED_PHASE, _ALLOWED_SAFE_GATES, _inverse_gate


def is_safe_program(effect: Effect, ops: Sequence[Op]) -> bool:
    """Check whether an IR program is safe (coherent + well-formed ancilla blocks)."""
    if effect is not Effect.COHERENT:
        return False
    return _ops_are_safe(ops)


def _ops_are_safe(ops: Sequence[Op]) -> bool:
    for op in ops:
        if isinstance(op, GateOp):
            if op.name not in _ALLOWED_SAFE_GATES:
                return False
            continue
        elif isinstance(op, AncillaBlockOp):
            for g in op.compute_ops:
                if not isinstance(g, GateOp) or g.name not in _ALLOWED_COMPUTE:
                    return False
            for g in op.phase_ops:
                if not isinstance(g, GateOp) or g.name not in _ALLOWED_PHASE:
                    return False
            if len(op.uncompute_ops) != len(op.compute_ops):
                return False
            for uc, c in zip(op.uncompute_ops, reversed(op.compute_ops)):
                if not isinstance(uc, GateOp):
                    return False
                expected = _inverse_gate(c)
                if uc.name != expected.name or uc.wires != expected.wires or uc.params != expected.params:
                    return False
        elif isinstance(op, ParOp):
            if not _ops_are_safe(op.left_ops) or not _ops_are_safe(op.right_ops):
                return False
        else:
            return False
    return True
