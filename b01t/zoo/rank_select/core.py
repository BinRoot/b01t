"""Rank-select: coherent legal-action indexing (QCE26, Section 4.1).

Two output encodings:

  rank_select():        one-hot output (N qubits), O(1) per-cell application;
                        sentinel (no valid action) is the all-zero vector.
  rank_select_binary(): binary output (ceil(log2(N+1)) qubits), O(N)
                        application; sentinel is the binary encoding of N.

Both are @coherent with internal ancilla management.
"""

from math import ceil, log2

from b01t.core import QReg, Wire, coherent, primitive, cx, x
from b01t.kit import ancilla, compute, apply, uncompute
from b01t.kit.arithmetic import (
    apply_pattern_x_wires,
    int_to_bits,
    controlled_inc_wires,
    controlled_dec_wires,
)


def rank_select_scan(
    occ_wires: list[Wire],
    sel_wires: list[Wire],
    move_wires: list[Wire],
    pre_wires: list[Wire],
    eq_wires: list[Wire],
    n_cells: int,
) -> None:
    """Internal forward/reverse scan. Plain function that emits gates.

    Sets move_wires[cell] = 1 for the selector-th empty cell.
    Cleans up pre_wires and eq_wires internally.

    Used inside compute() blocks. This is not the paper's interface;
    use rank_select() for the full certified pattern.
    """
    w = len(pre_wires)

    for cell in range(n_cells):
        x(occ_wires[cell])
        for bit in range(w):
            cx(pre_wires[bit], eq_wires[bit])
            cx(sel_wires[bit], eq_wires[bit])
        for bit in range(w):
            x(eq_wires[bit])
        all_controls = [occ_wires[cell]] + eq_wires
        apply_pattern_x_wires(all_controls, [1] * len(all_controls), move_wires[cell])
        for bit in range(w):
            x(eq_wires[bit])
        for bit in range(w):
            cx(sel_wires[bit], eq_wires[bit])
            cx(pre_wires[bit], eq_wires[bit])
        controlled_inc_wires(occ_wires[cell], pre_wires)
        x(occ_wires[cell])

    for cell in reversed(range(n_cells)):
        x(occ_wires[cell])
        controlled_dec_wires(occ_wires[cell], pre_wires)
        x(occ_wires[cell])


def rank_select_binary_scan(
    occ_wires: list[Wire],
    sel_wires: list[Wire],
    flag_wire: Wire,
    idx_wires: list[Wire],
    pre_wires: list[Wire],
    eq_wires: list[Wire],
    n_cells: int,
) -> None:
    """Forward/reverse scan that writes matching cell index to idx_wires,
    or the sentinel value ``n_cells`` when no cell matches.

    Pre-loads idx to binary(n_cells); on a match at cell c, XORs with
    (c XOR n_cells) so idx ends at binary(c). With no match, idx keeps
    its pre-loaded sentinel value.

    After completion: flag=0, pre=0, eq=0, idx=cell_index_of_match
    (or ``n_cells`` if no valid cell exists at the requested rank).
    """
    w = len(pre_wires)
    idx_w = len(idx_wires)
    sentinel_bits = int_to_bits(n_cells, idx_w)

    # Preload sentinel into idx.
    for bit in range(idx_w):
        if sentinel_bits[bit]:
            x(idx_wires[bit])

    for cell in range(n_cells):
        x(occ_wires[cell])
        # Check prefix == selector → eq
        for bit in range(w):
            cx(pre_wires[bit], eq_wires[bit])
            cx(sel_wires[bit], eq_wires[bit])
        for bit in range(w):
            x(eq_wires[bit])
        # All-1 check → flag
        all_controls = [occ_wires[cell]] + eq_wires
        apply_pattern_x_wires(all_controls, [1] * len(all_controls), flag_wire)
        # Rewrite idx from sentinel to cell index when flagged.
        cell_bits = int_to_bits(cell, idx_w)
        for bit in range(idx_w):
            if cell_bits[bit] != sentinel_bits[bit]:
                cx(flag_wire, idx_wires[bit])
        # Unset flag
        apply_pattern_x_wires(all_controls, [1] * len(all_controls), flag_wire)
        # Undo eq check
        for bit in range(w):
            x(eq_wires[bit])
        for bit in range(w):
            cx(sel_wires[bit], eq_wires[bit])
            cx(pre_wires[bit], eq_wires[bit])
        # Increment prefix if empty
        controlled_inc_wires(occ_wires[cell], pre_wires)
        x(occ_wires[cell])

    # Reverse scan to clean prefix
    for cell in reversed(range(n_cells)):
        x(occ_wires[cell])
        controlled_dec_wires(occ_wires[cell], pre_wires)
        x(occ_wires[cell])


@coherent
def rank_select_binary(
    occ: QReg,
    selector: QReg,
    target: QReg,
) -> None:
    """Coherent rank-select with binary-encoded output.

    Selects the selector-th empty cell and writes its cell index
    (binary-encoded) to the target register. For out-of-range ranks
    the target receives the sentinel value ``N = len(occ)``; downstream
    circuits treat this as a designated no-op branch.

    Target width must be at least ``ceil(log2(N+1))`` bits to
    represent the sentinel.

    Args:
        occ: occupancy register (which cells are occupied)
        selector: which empty cell to select (rank index)
        target: output register (binary cell index, width
            ``ceil(log2(N+1))`` or more)
    """
    n = len(occ)
    w = len(selector)
    idx_w = len(target)
    required_w = max(1, ceil(log2(n + 1)))
    assert idx_w >= required_w, (
        f"rank_select_binary: target width {idx_w} too small for "
        f"sentinel N={n}; need at least {required_w}")

    # Ancilla: 1 flag + w prefix + w eq + idx_w idx
    with ancilla(1 + w + w + idx_w) as scratch:
        flag = scratch.wires()[0]
        pre = scratch.wires()[1:1 + w]
        eq = scratch.wires()[1 + w:1 + 2 * w]
        idx = scratch.wires()[1 + 2 * w:]
        compute(lambda: rank_select_binary_scan(
            occ.wires(), selector.wires(), flag, idx, pre, eq, n))
        apply(lambda: [cx(idx[bit], target[bit]) for bit in range(idx_w)])
        uncompute()


@coherent
def rank_select(
    occ: QReg,
    selector: QReg,
    target: QReg,
) -> None:
    """Coherent rank-select (paper eq. 1, Theorem 1).

    Selects the selector-th empty cell and applies CX to the target
    register. All ancillae (move flags, prefix counter, eq scratch)
    are allocated internally and fully uncomputed.

    Structurally certified ancilla-clean via compute/apply/uncompute
    discipline, justified by cma_ancilla_clean_product (AncillaApply.lean).

    Args:
        occ: occupancy register (which cells are occupied)
        selector: which empty cell to select (rank index)
        target: output register (one-hot)
    """
    n = len(occ)
    w = len(selector)

    with ancilla(n + w + w) as scratch:
        mv = scratch.wires()[:n]
        pre = scratch.wires()[n:n+w]
        eq = scratch.wires()[n+w:]
        compute(lambda: rank_select_scan(
            occ.wires(), selector.wires(), mv, pre, eq, n))
        apply(lambda: [cx(mv[cell], target[cell]) for cell in range(n)])
        uncompute()
