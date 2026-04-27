"""Rank-select: coherent legal-action indexing (QCE26, Section 4.1).

Two output encodings:

  rank_select():        one-hot output (N qubits), O(1) per-cell application;
                        sentinel (no valid action) is the all-zero vector.
  rank_select_binary(): binary output (ceil(log2(N+1)) qubits), O(N)
                        application; sentinel is the binary encoding of N.

Both are @coherent with internal ancilla management.
"""

from math import ceil, log2

from b01t.core import QReg, Wire, coherent, primitive, cx, ccx, x
from b01t.kit import ancilla, compute, apply, uncompute
from b01t.kit.arithmetic import (
    apply_pattern_x_wires,
    int_to_bits,
    controlled_inc_wires,
    controlled_dec_wires,
    ripple_carry_add_wires,
)
from b01t.kit.arithmetic.comparator import _borrow_chain_wires


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


def _next_pow_2_at_least(x: int) -> int:
    if x <= 1:
        return 1
    p = 1
    while p < x:
        p *= 2
    return p


@coherent
def rank_select_binary_blocked(
    occ: QReg,
    selector: QReg,
    target: QReg,
) -> None:
    """Coherent rank-select via the blocked construction (Theorem 7).

    Functionally identical to ``rank_select_binary`` on every basis
    state. Implements the unrestricted-layout block decomposition: split
    the validity register into blocks of size ``B = next_pow_of_2(w)``,
    compute per-block popcounts and take-flags, run the inner scan
    unconditionally on each block, and gate only the final output write
    on the take-flag.

    The inner rank-select scan is shared with ``rank_select_binary``
    (``rank_select_binary_scan``) via the prefix-counter trick: the
    inner scan's ``pre`` register is shared with the running prefix
    counter ``p``, so a match in block ``q`` fires when the global
    prefix count equals the selector.

    Args:
        occ: occupancy register (which cells are occupied)
        selector: which empty cell to select (rank index)
        target: output register (binary cell index, width
            ``ceil(log2(N+1))`` or more, preloaded with sentinel ``N``).
    """
    n = len(occ)
    w = len(selector)
    idx_w = len(target)
    required_w = max(1, ceil(log2(n + 1)))
    assert idx_w >= required_w, (
        f"rank_select_binary_blocked: target width {idx_w} too small "
        f"for sentinel N={n}; need at least {required_w}")

    if n == 0 or w == 0:
        return

    B = _next_pow_2_at_least(w)
    L = (n + B - 1) // B
    inner_w = max(1, ceil(log2(B + 1)))

    sentinel_bits = int_to_bits(n, idx_w)
    sel_wires = selector.wires()
    occ_wires = occ.wires()
    target_wires = target.wires()

    # Per-block ancilla layout (in order):
    #   cq          [w]
    #   pcq         [w]
    #   take_q      [1]
    #   inner_idx   [inner_w]
    #   inner_flag  [1]
    #   eq          [w]            (inner-scan eq scratch)
    #   borrow_p    [w]            (less_than scratch for sel<p)
    #   borrow_pcq  [w]            (less_than scratch for sel<pcq)
    per_block = 5 * w + inner_w + 2
    # Shared:
    #   p   [w]
    #   cin [1]
    shared = w + 1
    total_anc = shared + L * per_block

    with ancilla(total_anc) as scratch:
        wires = scratch.wires()

        p = wires[0:w]
        cin = wires[w]

        def slot(q: int):
            base = w + 1 + q * per_block
            return {
                "cq":         wires[base                  : base + w],
                "pcq":        wires[base + w              : base + 2 * w],
                "take":       wires[base + 2 * w],
                "idx":        wires[base + 2 * w + 1      : base + 2 * w + 1 + inner_w],
                "flag":       wires[base + 2 * w + 1 + inner_w],
                "eq":         wires[base + 2 * w + 2 + inner_w : base + 3 * w + 2 + inner_w],
                "borrow_p":   wires[base + 3 * w + 2 + inner_w : base + 4 * w + 2 + inner_w],
                "borrow_pcq": wires[base + 4 * w + 2 + inner_w : base + 5 * w + 2 + inner_w],
            }

        slots = [slot(q) for q in range(L)]

        def emit_compute() -> None:
            for q in range(L):
                s = slots[q]
                start = q * B
                end = min(start + B, n)
                actual = end - start
                block_occ = occ_wires[start:end]

                # (a) c_q = popcount of valid (= 1 after flip) cells
                for c in block_occ:
                    x(c)
                    controlled_inc_wires(c, s["cq"])
                    x(c)

                # (b) pcq = p + c_q  (copy p into pcq, then add c_q)
                for i in range(w):
                    cx(p[i], s["pcq"][i])
                ripple_carry_add_wires(s["cq"], s["pcq"], cin)

                # (c) borrow chain for (sel < p):  result on borrow_p[w-1]
                _borrow_chain_wires(sel_wires, p, s["borrow_p"])

                # (d) borrow chain for (sel < pcq): result on borrow_pcq[w-1]
                _borrow_chain_wires(sel_wires, s["pcq"], s["borrow_pcq"])

                # (e) take_q = (NOT lt_p) AND lt_pcq
                lt_p = s["borrow_p"][w - 1]
                lt_pcq = s["borrow_pcq"][w - 1]
                x(lt_p)
                ccx(lt_p, lt_pcq, s["take"])
                x(lt_p)

                # (f) Inner rank-select scan on the block.
                # Shares p as the inner prefix counter: a match fires when
                # p (incremented per valid bit) equals the selector,
                # i.e., at the (sel - p_initial)-th valid cell in the block.
                # The scan's cleanup pass restores p to its initial value.
                rank_select_binary_scan(
                    block_occ, sel_wires, s["flag"], s["idx"],
                    p, s["eq"], actual)

                # (g) p <- p + c_q  (running prefix counter advances)
                ripple_carry_add_wires(s["cq"], p, cin)

        def emit_apply() -> None:
            # Preload sentinel N into target. The per-block controlled
            # writes XOR (q*B + inner_idx) ^ N, so on the firing block
            # this transitions target from N to (q*B + inner_idx).
            # If no block fires (out-of-range rank), target stays at N.
            for i in range(idx_w):
                if sentinel_bits[i]:
                    x(target_wires[i])
            for q in range(L):
                s = slots[q]
                qB = q * B
                # target ^= (q*B + inner_idx) ^ N gated on take_q.
                # B is a power of 2, so q*B + inner_idx = q*B XOR inner_idx
                # at the bit level (low inner_w bits = inner_idx, high bits = q).
                for i in range(idx_w):
                    qB_bit = (qB >> i) & 1
                    N_bit = sentinel_bits[i]
                    const_bit = qB_bit ^ N_bit
                    if const_bit:
                        cx(s["take"], target_wires[i])
                    if i < inner_w:
                        ccx(s["take"], s["idx"][i], target_wires[i])

        compute(emit_compute)
        apply(emit_apply)
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
