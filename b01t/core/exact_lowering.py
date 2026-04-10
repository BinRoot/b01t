"""Lower ExactProgram to broad IRProgram for backends."""

from .types import (
    Effect, Wire, QReg, GateOp, AncillaBlockOp, ParOp, Op, IRProgram,
)
from .exact_types import (
    ExactGate, ExactGateOp, ExactAncillaBlock, ExactParOp, ExactOp, ExactProgram,
)


# ---------------------------------------------------------------------------
# ExactGate -> broad gate name
# ---------------------------------------------------------------------------

_EXACT_TO_NAME: dict[ExactGate, str] = {
    ExactGate.X: "x", ExactGate.H: "h", ExactGate.Z: "z",
    ExactGate.S: "s", ExactGate.SDG: "sdg", ExactGate.T: "t", ExactGate.TDG: "tdg",
    ExactGate.CX: "cx", ExactGate.CZ: "cz", ExactGate.SWAP: "swap",
    ExactGate.CCX: "ccx", ExactGate.CCZ: "ccz",
    ExactGate.MCX: "mcx", ExactGate.MCZ: "mcz",
}


# ---------------------------------------------------------------------------
# Ancilla coalescing (sequential only; par branches stay disjoint)
# ---------------------------------------------------------------------------

def _collect_sequential_anc_regs(
    ops: tuple[ExactOp, ...] | list[ExactOp],
) -> list[QReg]:
    """Collect ancilla registers that can be safely coalesced.

    Only registers at the same sequential level are collected.
    Registers inside par branches are NOT included; they are
    handled separately within each branch.
    """
    seen: set[str] = set()
    regs: list[QReg] = []
    for op in ops:
        if isinstance(op, ExactAncillaBlock):
            if op.ancilla.name not in seen:
                seen.add(op.ancilla.name)
                regs.append(op.ancilla)
        # Deliberately skip ExactParOp: ancillae inside par branches
        # must not be coalesced with registers at this level or in the
        # other branch. Each branch handles its own coalescing.
    return regs


def _build_wire_remap(anc_regs: list[QReg]) -> tuple[QReg | None, dict[Wire, Wire]]:
    """Build a wire remap that maps all ancilla registers to the largest one."""
    if not anc_regs:
        return None, {}
    largest = max(anc_regs, key=lambda r: r.size)
    remap: dict[Wire, Wire] = {}
    for reg in anc_regs:
        if reg.name == largest.name:
            continue
        for i in range(reg.size):
            old = Wire(reg.name, i, reg.kind)
            new = Wire(largest.name, i, largest.kind)
            remap[old] = new
    return largest, remap


def _remap_wire(w: Wire, remap: dict[Wire, Wire]) -> Wire:
    return remap.get(w, w)


def _remap_wires(wires: tuple[Wire, ...], remap: dict[Wire, Wire]) -> tuple[Wire, ...]:
    return tuple(_remap_wire(w, remap) for w in wires)


# ---------------------------------------------------------------------------
# Lowering
# ---------------------------------------------------------------------------

def _lower_gate(eop: ExactGateOp, remap: dict[Wire, Wire]) -> GateOp:
    return GateOp(
        name=_EXACT_TO_NAME[eop.gate],
        wires=_remap_wires(eop.wires, remap),
        params=(),
    )


def _lower_ops(
    ops: tuple[ExactOp, ...] | list[ExactOp],
    remap: dict[Wire, Wire],
    largest_anc: QReg | None,
) -> list[Op]:
    result: list[Op] = []
    for op in ops:
        if isinstance(op, ExactGateOp):
            result.append(_lower_gate(op, remap))
        elif isinstance(op, ExactAncillaBlock):
            anc = largest_anc if largest_anc is not None else op.ancilla
            # middle_ops maps to broad phase_ops. For APPLY-pattern blocks,
            # these may contain non-diagonal gates (permutation gates on
            # disjoint system wires). This is intentional: the broad IR is
            # for execution only, not re-verification. Safety was proven by
            # the exact AST. Do not run is_safe_program() on lowered IR.
            result.append(AncillaBlockOp(
                ancilla=anc,
                compute_ops=[_lower_gate(g, remap) for g in op.compute_ops],
                phase_ops=[_lower_gate(g, remap) for g in op.middle_ops],
                uncompute_ops=[_lower_gate(g, remap) for g in op.uncompute_ops],
            ))
        elif isinstance(op, ExactParOp):
            # Each par branch gets its own coalescing scope.
            left_anc_regs = _collect_sequential_anc_regs(op.left_ops)
            right_anc_regs = _collect_sequential_anc_regs(op.right_ops)

            left_largest, left_remap = _build_wire_remap(left_anc_regs)
            right_largest, right_remap = _build_wire_remap(right_anc_regs)

            # Merge parent remap with branch-local remap
            left_full = {**remap, **left_remap}
            right_full = {**remap, **right_remap}

            result.append(ParOp(
                left_ops=_lower_ops(op.left_ops, left_full, left_largest),
                right_ops=_lower_ops(op.right_ops, right_full, right_largest),
            ))
    return result


def _collect_all_anc_regs(
    ops: tuple[ExactOp, ...] | list[ExactOp],
) -> list[QReg]:
    """Collect ALL ancilla registers (including inside par) for the
    final register list. Does not affect coalescing; it only ensures all
    ancilla registers appear in the IR program's register list."""
    seen: set[str] = set()
    regs: list[QReg] = []
    for op in ops:
        if isinstance(op, ExactAncillaBlock):
            if op.ancilla.name not in seen:
                seen.add(op.ancilla.name)
                regs.append(op.ancilla)
        elif isinstance(op, ExactParOp):
            for r in _collect_all_anc_regs(op.left_ops):
                if r.name not in seen:
                    seen.add(r.name)
                    regs.append(r)
            for r in _collect_all_anc_regs(op.right_ops):
                if r.name not in seen:
                    seen.add(r.name)
                    regs.append(r)
    return regs


# ---------------------------------------------------------------------------
# Public API
# ---------------------------------------------------------------------------

def lower_exact_program(prog: ExactProgram) -> IRProgram:
    """Convert an ``ExactProgram`` to a broad ``IRProgram`` for backend execution.

    Ancilla coalescing: sequential ancilla registers share physical qubits.
    Par branches keep their ancillae separate (disjoint Hilbert spaces).

    The returned IR has ``is_safe=True`` because the ``ExactProgram`` was
    certified by the exact path. Do not re-check with ``is_safe_program()``,
    because the broad-path checker does not understand APPLY-pattern ancilla blocks
    and will give a false negative.
    """
    # Top-level sequential coalescing
    seq_anc_regs = _collect_sequential_anc_regs(prog.ops)
    largest_anc, remap = _build_wire_remap(seq_anc_regs)

    # Collect all ancilla registers (including inside par) for the register list
    all_anc = _collect_all_anc_regs(prog.ops)

    # Build the register list: system regs + coalesced/uncoalesced ancilla regs
    regs = [r for r in prog.regs if r.kind != "anc"]
    seen_anc: set[str] = set()
    if largest_anc is not None:
        regs.append(largest_anc)
        seen_anc.add(largest_anc.name)
        # Add remapped (smaller sequential) registers' names to seen
        for r in seq_anc_regs:
            seen_anc.add(r.name)
    # Add any ancilla registers from par branches that weren't coalesced
    for r in all_anc:
        if r.name not in seen_anc:
            regs.append(r)
            seen_anc.add(r.name)

    return IRProgram(
        name=prog.name,
        effect=Effect.COHERENT,
        regs=regs,
        ops=_lower_ops(prog.ops, remap, largest_anc),
        is_safe=True,
    )
