"""Controlled-call utility: emit a @coherent function's gates controlled on an extra qubit.

Captures the ExactOps of a @coherent function by running it inside a
temporary exact build context, then re-emits each gate as its controlled
variant into the current @parametric broad-path context.

This is the mechanism that lets coherent amplitude estimation (QPE on
the Grover iterate) apply controlled-G^(2^k) without a generic
"controlled unitary" gate primitive.
"""

import math
from typing import Callable, Union

from b01t.core.types import Wire, QReg
from b01t.core.exact_types import (
    ExactGate, ExactGateOp, ExactAncillaBlock, ExactParOp, ExactOp,
)
from b01t.core.exact_builder import (
    ExactDSLFunction, _ExactBuildContext, _push_exact_ctx,
)
from b01t.core.builder import _ctx as _broad_ctx
from b01t.core.gates import (
    x, h, z, s, sdg, t, tdg,
    cx, cz, swap, ccx, ccz, mcx, mcz,
    rz, crz,
)


# ---------------------------------------------------------------------------
# Gate control-lifting: ExactGate -> broad-path controlled equivalent
# ---------------------------------------------------------------------------

def _emit_controlled_gate(ctrl: Wire, eop: ExactGateOp) -> None:
    """Emit one ExactGateOp controlled on *ctrl* into the broad context."""
    g = eop.gate
    w = eop.wires

    # -- Single-qubit permutation / Pauli --
    if g == ExactGate.X:
        cx(ctrl, w[0])
    elif g == ExactGate.Z:
        cz(ctrl, w[0])

    # -- Hadamard: standard CH decomposition --
    # CH = Sdg T H CX T H S  (textbook, up to global phase)
    elif g == ExactGate.H:
        # Decompose controlled-H on (ctrl, target=w[0])
        # Using: Ry(-pi/4) . CNOT . Ry(pi/4) is NOT exact.
        # Exact decomposition (all gates in the broad set):
        #   S†(t); H(t); T†(t); CX(c,t); T(t); H(t); S(t)
        sdg(w[0])
        h(w[0])
        tdg(w[0])
        cx(ctrl, w[0])
        t(w[0])
        h(w[0])
        s(w[0])

    # -- Phase gates via C-Phase(theta) decomposition --
    # C-Phase(theta) = Rz(theta/2, t) . CX(c,t) . Rz(-theta/2, t) .
    #                  CX(c,t) . Rz(theta/2, c)
    elif g == ExactGate.S:
        _c_phase(ctrl, w[0], math.pi / 2)
    elif g == ExactGate.SDG:
        _c_phase(ctrl, w[0], -math.pi / 2)
    elif g == ExactGate.T:
        _c_phase(ctrl, w[0], math.pi / 4)
    elif g == ExactGate.TDG:
        _c_phase(ctrl, w[0], -math.pi / 4)

    # -- Two-qubit: add one control --
    elif g == ExactGate.CX:
        ccx(ctrl, w[0], w[1])
    elif g == ExactGate.CZ:
        ccz(ctrl, w[0], w[1])
    elif g == ExactGate.SWAP:
        # Fredkin (controlled-SWAP): CX(b,a); CCX(ctrl,a,b); CX(b,a)
        cx(w[1], w[0])
        ccx(ctrl, w[0], w[1])
        cx(w[1], w[0])

    # -- Three-qubit: promote to MCX/MCZ --
    elif g == ExactGate.CCX:
        mcx([ctrl, w[0], w[1]], w[2])
    elif g == ExactGate.CCZ:
        # MCZ via H-MCX-H
        h(w[2])
        mcx([ctrl, w[0], w[1]], w[2])
        h(w[2])

    # -- Multi-controlled: prepend ctrl --
    elif g == ExactGate.MCX:
        mcx([ctrl] + list(w[:-1]), w[-1])
    elif g == ExactGate.MCZ:
        h(w[-1])
        mcx([ctrl] + list(w[:-1]), w[-1])
        h(w[-1])

    else:
        raise ValueError(f"controlled_call: unsupported gate {g}")


def _c_phase(ctrl: Wire, target: Wire, theta: float) -> None:
    """Emit C-Phase(theta) = controlled diagonal phase rotation."""
    rz(theta / 2, target)
    cx(ctrl, target)
    rz(-theta / 2, target)
    cx(ctrl, target)
    rz(theta / 2, ctrl)


# ---------------------------------------------------------------------------
# Recursive op walker
# ---------------------------------------------------------------------------

def _emit_controlled_ops(
    ctrl: Wire,
    ops: tuple[ExactOp, ...] | list[ExactOp],
    broad_ctx,
) -> None:
    """Walk the ExactOp tree and emit each gate controlled on *ctrl*."""
    for op in ops:
        if isinstance(op, ExactGateOp):
            _emit_controlled_gate(ctrl, op)

        elif isinstance(op, ExactAncillaBlock):
            # Register ancilla QReg in the broad context so wire
            # validation passes when we emit controlled gates.
            if op.ancilla not in broad_ctx.regs:
                broad_ctx.regs.append(op.ancilla)
            # Flatten: compute + middle + uncompute, all controlled.
            # Correctness: ctrl=|0> -> no gates fire, ancilla stays |0>.
            #              ctrl=|1> -> full cycle, ancilla returns to |0>.
            _emit_controlled_ops(ctrl, op.compute_ops, broad_ctx)
            _emit_controlled_ops(ctrl, op.middle_ops, broad_ctx)
            _emit_controlled_ops(ctrl, op.uncompute_ops, broad_ctx)

        elif isinstance(op, ExactParOp):
            _emit_controlled_ops(ctrl, op.left_ops, broad_ctx)
            _emit_controlled_ops(ctrl, op.right_ops, broad_ctx)

        else:
            raise ValueError(f"controlled_call: unsupported op type {type(op)}")


# ---------------------------------------------------------------------------
# Uncontrolled exact-op emitter (for inline_exact)
# ---------------------------------------------------------------------------

_EXACT_TO_BROAD: dict[ExactGate, str] = {
    ExactGate.X: "x", ExactGate.H: "h", ExactGate.Z: "z",
    ExactGate.S: "s", ExactGate.SDG: "sdg", ExactGate.T: "t", ExactGate.TDG: "tdg",
    ExactGate.CX: "cx", ExactGate.CZ: "cz", ExactGate.SWAP: "swap",
    ExactGate.CCX: "ccx", ExactGate.CCZ: "ccz",
    ExactGate.MCX: "mcx", ExactGate.MCZ: "mcz",
}


def _emit_exact_gate(eop: ExactGateOp) -> None:
    """Emit one ExactGateOp as its broad-path equivalent."""
    from b01t.core.builder import _append_op
    from b01t.core.types import GateOp
    name = _EXACT_TO_BROAD[eop.gate]
    _append_op(GateOp(name=name, wires=eop.wires, params=()))


def _emit_exact_ops(
    ops: tuple[ExactOp, ...] | list[ExactOp],
    broad_ctx,
) -> None:
    """Walk the ExactOp tree and emit each gate as a broad-path op."""
    for op in ops:
        if isinstance(op, ExactGateOp):
            _emit_exact_gate(op)
        elif isinstance(op, ExactAncillaBlock):
            if op.ancilla not in broad_ctx.regs:
                broad_ctx.regs.append(op.ancilla)
            _emit_exact_ops(op.compute_ops, broad_ctx)
            _emit_exact_ops(op.middle_ops, broad_ctx)
            _emit_exact_ops(op.uncompute_ops, broad_ctx)
        elif isinstance(op, ExactParOp):
            _emit_exact_ops(op.left_ops, broad_ctx)
            _emit_exact_ops(op.right_ops, broad_ctx)
        else:
            raise ValueError(f"inline_exact: unsupported op type {type(op)}")


def _capture_exact_ops(fn, qregs, broad_ctx):
    """Push a temp exact context, run fn, return captured ExactOps."""
    raw_fn = getattr(fn, 'fn', fn)
    temp_ctx = _ExactBuildContext(
        fn_name=f"<capture:{getattr(fn, '__name__', 'anon')}>",
        regs=list(broad_ctx.regs),
    )
    with _push_exact_ctx(temp_ctx):
        raw_fn(*qregs)
    return temp_ctx


# ---------------------------------------------------------------------------
# Public API
# ---------------------------------------------------------------------------

def inline_exact(fn: Union[ExactDSLFunction, Callable], *qregs: QReg) -> None:
    """Emit *fn(*qregs)* as flat broad-path gates in the current context.

    Use this to call a ``@coherent`` function from a ``@parametric``
    context when the function uses the ``apply`` (CMA) ancilla pattern,
    which the broad path doesn't support natively.

    The exact ops are captured via a temporary exact context, then
    re-emitted as broad-path ``GateOp`` objects (ancilla blocks are
    flattened into their constituent gate sequences).
    """
    broad = _broad_ctx()
    temp_ctx = _capture_exact_ops(fn, qregs, broad)
    _emit_exact_ops(temp_ctx.ops, broad)


def controlled_call(ctrl: Wire, fn: Union[ExactDSLFunction, Callable], *qregs: QReg) -> None:
    """Emit *fn(*qregs)* with every gate controlled on *ctrl*.

    Must be called inside a ``@parametric`` build context.  *fn* must
    be a ``@coherent`` ``ExactDSLFunction`` (or a raw callable that
    emits exact gates).

    Mechanism:
    1. Push a temporary ``_ExactBuildContext`` with the caller's QRegs.
    2. Run *fn* — gate calls route to the exact context and are captured.
    3. Walk the captured ``ExactOp`` tree; for each gate emit the
       controlled variant as broad-path gate calls (which land in the
       enclosing ``@parametric`` context).
    """
    broad = _broad_ctx()  # must be inside @parametric
    temp_ctx = _capture_exact_ops(fn, qregs, broad)
    _emit_controlled_ops(ctrl, temp_ctx.ops, broad)
