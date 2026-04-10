"""Validate exact programs and define exact inverse rules."""

from typing import Sequence

from .types import DSLValidationError, QReg, Wire
from .exact_types import (
    ExactGate, ExactGateOp, ExactAncillaBlock, ExactParOp, ExactOp,
    MiddleBlockKind, EXACT_COMPUTE_GATES, EXACT_PHASE_GATES,
)


# ---------------------------------------------------------------------------
# Self-inverse / inverse-pair tables for exact gates
# ---------------------------------------------------------------------------

_EXACT_SELF_INVERSE = frozenset({
    ExactGate.X, ExactGate.H, ExactGate.Z,
    ExactGate.CX, ExactGate.CZ, ExactGate.SWAP,
    ExactGate.CCX, ExactGate.CCZ,
    ExactGate.MCX, ExactGate.MCZ,
})

_EXACT_INVERSE_PAIRS = {
    ExactGate.S: ExactGate.SDG,
    ExactGate.SDG: ExactGate.S,
    ExactGate.T: ExactGate.TDG,
    ExactGate.TDG: ExactGate.T,
}


def exact_inverse_gate(op: ExactGateOp) -> ExactGateOp:
    """Return the exact inverse of a single gate op."""
    if op.gate in _EXACT_SELF_INVERSE:
        return ExactGateOp(op.gate, op.wires)
    if op.gate in _EXACT_INVERSE_PAIRS:
        return ExactGateOp(_EXACT_INVERSE_PAIRS[op.gate], op.wires)
    raise DSLValidationError(f"no exact inverse for gate {op.gate}")


def exact_inverse_ops(ops: Sequence[ExactOp]) -> list[ExactOp]:
    """Reverse a list of exact ops and invert each one."""
    result: list[ExactOp] = []
    for op in reversed(ops):
        if isinstance(op, ExactGateOp):
            result.append(exact_inverse_gate(op))
        elif isinstance(op, ExactAncillaBlock):
            result.append(ExactAncillaBlock(
                ancilla=op.ancilla,
                compute_ops=tuple(exact_inverse_gate(g) for g in reversed(op.uncompute_ops)),
                middle_ops=tuple(exact_inverse_gate(g) for g in reversed(op.middle_ops)),
                uncompute_ops=tuple(exact_inverse_gate(g) for g in reversed(op.compute_ops)),
                middle_kind=op.middle_kind,
            ))
        elif isinstance(op, ExactParOp):
            result.append(ExactParOp(
                left_ops=tuple(exact_inverse_ops(op.left_ops)),
                right_ops=tuple(exact_inverse_ops(op.right_ops)),
            ))
        else:
            raise DSLValidationError(f"exact adjoint does not support {type(op).__name__}")
    return result


# ---------------------------------------------------------------------------
# Wire validation
# ---------------------------------------------------------------------------

def validate_wires_declared(wires: tuple[Wire, ...], regs: Sequence[QReg]) -> None:
    """Every wire must reference a declared register with valid index."""
    reg_map = {r.name: r for r in regs}
    for w in wires:
        if w.reg not in reg_map:
            raise DSLValidationError(
                f"wire references undeclared register '{w.reg}'")
        if w.index < 0 or w.index >= reg_map[w.reg].size:
            raise DSLValidationError(
                f"wire {w} index out of range for register '{w.reg}' (size {reg_map[w.reg].size})")


def validate_wires_distinct(wires: tuple[Wire, ...]) -> None:
    """Multi-qubit gates require pairwise distinct wires."""
    if len(wires) > 1 and len(set(wires)) != len(wires):
        raise DSLValidationError("multi-qubit gate requires distinct wires")


# ---------------------------------------------------------------------------
# Collect wires (for par disjointness)
# ---------------------------------------------------------------------------

def collect_exact_wires(ops: Sequence[ExactOp]) -> set[Wire]:
    """Collect all wires referenced in a sequence of exact ops."""
    wires: set[Wire] = set()
    for op in ops:
        if isinstance(op, ExactGateOp):
            wires.update(op.wires)
        elif isinstance(op, ExactAncillaBlock):
            for g in op.compute_ops:
                wires.update(g.wires)
            for g in op.middle_ops:
                wires.update(g.wires)
            for g in op.uncompute_ops:
                wires.update(g.wires)
        elif isinstance(op, ExactParOp):
            wires.update(collect_exact_wires(op.left_ops))
            wires.update(collect_exact_wires(op.right_ops))
    return wires


def validate_par_disjoint(left: Sequence[ExactOp], right: Sequence[ExactOp]) -> None:
    """Par branches must operate on wire-disjoint sets."""
    overlap = collect_exact_wires(left) & collect_exact_wires(right)
    if overlap:
        labels = ", ".join(str(w) for w in sorted(overlap, key=str))
        raise DSLValidationError(
            f"par() requires disjoint wires, overlap on: {labels}")


# ---------------------------------------------------------------------------
# Ancilla block validation
# ---------------------------------------------------------------------------

def _collect_gate_wires(ops: Sequence[ExactGateOp]) -> set[Wire]:
    """Collect all wires from a flat list of gate ops."""
    wires: set[Wire] = set()
    for g in ops:
        wires.update(g.wires)
    return wires


# Gates that modify the computational basis state (non-diagonal).
# For these, one or more wires are "targets" (written to).
_PERMUTATION_TARGETS: dict[ExactGate, str] = {
    # Single-qubit: the wire is the target
    ExactGate.X: "all", ExactGate.H: "all",
    # Two-qubit: last wire is target
    ExactGate.CX: "last",
    # SWAP: both wires are targets
    ExactGate.SWAP: "all",
    # Three-qubit: last wire is target
    ExactGate.CCX: "last",
    # Multi-controlled: last wire is target
    ExactGate.MCX: "last",
}
# Diagonal gates (Z, S, T, CZ, CCZ, MCZ, SDG, TDG) have no targets -
# they only add phases, never change which basis state you're in.


def _target_wires(op: ExactGateOp) -> set[Wire]:
    """Return the set of wires MODIFIED by a gate (written to, not just read)."""
    kind = _PERMUTATION_TARGETS.get(op.gate)
    if kind is None:
        return set()  # diagonal gate, no target
    if kind == "all":
        return set(op.wires)
    if kind == "last":
        return {op.wires[-1]}
    return set()


def validate_ancilla_block(block: ExactAncillaBlock) -> None:
    """Validate gate sets, middle-block constraints, and uncompute correctness.

    For PHASE middle: gates must be in the exact diagonal phase set.
    For APPLY middle: gates must be on wires disjoint from compute wires
    (the PreservesFirst condition from cma_ancilla_clean_product).
    """
    for g in block.compute_ops:
        if g.gate not in EXACT_COMPUTE_GATES:
            raise DSLValidationError(
                f"gate {g.gate.name} is not allowed in exact compute blocks")

    if block.middle_kind == MiddleBlockKind.PHASE:
        for g in block.middle_ops:
            if g.gate not in EXACT_PHASE_GATES:
                raise DSLValidationError(
                    f"gate {g.gate.name} is not allowed in exact phase blocks")
    elif block.middle_kind == MiddleBlockKind.APPLY:
        # PreservesFirst (cma_ancilla_clean_product): M must not change the
        # first factor (sys_compute ⊗ ancilla). Two checks:
        #
        # 1. Apply ops must not share system wires with compute ops.
        # 2. Apply ops must not TARGET ancilla wires (may read them as controls).
        #
        # Target wire = the wire modified by the gate:
        #   Permutation gates (X, CX, CCX, MCX): last wire
        #   H: the wire (non-diagonal, modifies basis)
        #   SWAP: both wires
        #   Diagonal gates (Z, S, T, CZ, CCZ, etc.): no target (phase-only)
        anc_wires = set(Wire(block.ancilla.name, i, block.ancilla.kind)
                        for i in range(block.ancilla.size))

        # Check 1: system wire disjointness
        compute_sys_wires = _collect_gate_wires(block.compute_ops) - anc_wires
        apply_sys_wires = _collect_gate_wires(block.middle_ops) - anc_wires
        overlap = compute_sys_wires & apply_sys_wires
        if overlap:
            labels = ", ".join(str(w) for w in sorted(overlap, key=str))
            raise DSLValidationError(
                f"apply() block shares system wires with compute() block: {labels}. "
                f"apply() must operate on system wires disjoint from compute (PreservesFirst condition)")

        # Check 2: no apply op targets an ancilla wire
        for g in block.middle_ops:
            targets = _target_wires(g)
            anc_targets = targets & anc_wires
            if anc_targets:
                labels = ", ".join(str(w) for w in sorted(anc_targets, key=str))
                raise DSLValidationError(
                    f"apply() block modifies ancilla wire(s): {labels}. "
                    f"apply() may read ancilla wires as controls but must not write to them")

    if len(block.uncompute_ops) != len(block.compute_ops):
        raise DSLValidationError(
            "uncompute length does not match compute length")
    for uc, c in zip(block.uncompute_ops, reversed(block.compute_ops)):
        expected = exact_inverse_gate(c)
        if uc != expected:
            raise DSLValidationError(
                f"uncompute mismatch: expected {expected}, got {uc}")


# ---------------------------------------------------------------------------
# Full program validation
# ---------------------------------------------------------------------------

def validate_exact_ops(ops: Sequence[ExactOp], regs: Sequence[QReg]) -> None:
    """Recursively validate all ops in an exact program."""
    for op in ops:
        if isinstance(op, ExactGateOp):
            validate_wires_declared(op.wires, regs)
            validate_wires_distinct(op.wires)
        elif isinstance(op, ExactAncillaBlock):
            validate_ancilla_block(op)
            all_regs = list(regs) + [op.ancilla]
            for g in (*op.compute_ops, *op.middle_ops, *op.uncompute_ops):
                validate_wires_declared(g.wires, all_regs)
                validate_wires_distinct(g.wires)
        elif isinstance(op, ExactParOp):
            validate_par_disjoint(op.left_ops, op.right_ops)
            validate_exact_ops(op.left_ops, regs)
            validate_exact_ops(op.right_ops, regs)
        else:
            raise DSLValidationError(f"unknown exact op type: {type(op).__name__}")
