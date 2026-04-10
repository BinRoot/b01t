"""Ancilla discipline: compute / phase / uncompute."""

from typing import Any, Callable, Optional

from .types import DSLValidationError, AncillaBlockOp, QReg
from .gates import _validate_no_dirty_swap
from .builder import _ctx, _AncillaCapture, _fresh_anc_name_broad


class _AncillaManager:
    def __init__(self, size: int):
        self.size = size
        self.reg: Optional[QReg] = None

    def __enter__(self) -> QReg:
        ctx = _ctx()
        if ctx.ancilla is not None:
            raise DSLValidationError("nested ancilla blocks are not supported in the MVP")
        reg = QReg(name=_fresh_anc_name_broad(ctx), size=self.size, kind="anc")
        ctx.regs.append(reg)
        ctx.ancilla = _AncillaCapture(reg=reg)
        self.reg = reg
        return reg

    def __exit__(self, exc_type, exc, tb) -> None:
        ctx = _ctx()
        anc = ctx.ancilla
        try:
            if exc_type is None:
                if anc is None:
                    raise DSLValidationError("internal error: missing ancilla capture on exit")
                if anc.has_compute and not anc.has_uncompute:
                    raise DSLValidationError("ancilla block exited with incomplete compute/phase/uncompute cycle")
                if not anc.completed_stages:
                    raise DSLValidationError("ancilla block must contain at least one compute/phase/uncompute cycle")
                for compute_ops, phase_ops, uncompute_ops in anc.completed_stages:
                    ctx.ops.append(
                        AncillaBlockOp(
                            ancilla=anc.reg,
                            compute_ops=compute_ops,
                            phase_ops=phase_ops,
                            uncompute_ops=uncompute_ops,
                        )
                    )
        finally:
            ctx.ancilla = None
            ctx.mode = None


def ancilla(size: int) -> _AncillaManager:
    return _AncillaManager(size)


def compute(fn: Callable[[], Any]) -> None:
    ctx = _ctx()
    if ctx.ancilla is None:
        raise DSLValidationError("compute(...) must appear inside a with ancilla(k) block")
    if ctx.ancilla.has_compute:
        raise DSLValidationError("only one compute(...) call is allowed per ancilla block")
    if ctx.mode is not None:
        raise DSLValidationError("nested compute/phase sections are not supported")
    ctx.mode = "compute"
    try:
        fn()
    finally:
        ctx.mode = None
    _validate_no_dirty_swap(ctx.ancilla.compute_ops)
    ctx.ancilla.has_compute = True


def phase(fn: Callable[[], Any]) -> None:
    ctx = _ctx()
    if ctx.ancilla is None:
        raise DSLValidationError("phase(...) must appear inside a with ancilla(k) block")
    if ctx.ancilla.has_phase:
        raise DSLValidationError("only one phase(...) call is allowed per ancilla block")
    if not ctx.ancilla.has_compute:
        raise DSLValidationError("phase(...) must follow compute(...)")
    if ctx.mode is not None:
        raise DSLValidationError("nested compute/phase sections are not supported")
    ctx.mode = "phase"
    try:
        fn()
    finally:
        ctx.mode = None
    ctx.ancilla.has_phase = True


def uncompute() -> None:
    ctx = _ctx()
    if ctx.ancilla is None:
        raise DSLValidationError("uncompute() must appear inside a with ancilla(k) block")
    if not ctx.ancilla.has_compute:
        raise DSLValidationError("uncompute() requires a preceding compute(...)")
    if not ctx.ancilla.has_phase:
        raise DSLValidationError("uncompute() must follow phase(...)")
    if ctx.ancilla.has_uncompute:
        raise DSLValidationError("uncompute() must follow a new compute/phase cycle")
    ctx.ancilla.completed_stages.append((
        list(ctx.ancilla.compute_ops),
        list(ctx.ancilla.phase_ops),
        list(reversed(ctx.ancilla.compute_ops)),
    ))
    ctx.ancilla.compute_ops = []
    ctx.ancilla.phase_ops = []
    ctx.ancilla.has_compute = False
    ctx.ancilla.has_phase = False
    ctx.ancilla.has_uncompute = False
