"""One Sway transition step: stochastic color updates on occupied cells."""

from b01t import QReg, Wire, coherent, ancilla, compute, apply, uncompute, cx, x
from b01t.kit.arithmetic import (
    apply_pattern_x_wires,
    controlled_inc_wires,
    controlled_dec_wires,
    int_to_bits,
)
from .sway_spec import SwaySpec


def make_sway_transition(spec: SwaySpec):
    """Create a @coherent sway transition for the given spec."""
    neighbors = spec.neighbors()
    die_w = spec.die_width
    max_deg = spec.max_degree
    cw = spec.cnt_width

    @coherent
    def sway_transition(
        occ: QReg,
        color_src: QReg,
        color_dst: QReg,
        dice: QReg,
    ):
        """Apply one round of Sway stochastic transitions.

        For each cell:
          1. Copy color from src to dst
          2. Count friendly neighbors (compute)
          3. Compute flip flag from neighbor count and die roll (compute)
          4. Flip color_dst if flag is set (apply)
          5. Uncompute flag and neighbor count
        """
        n = len(occ)

        # Step 1: copy colors from src to dst
        for cell in range(n):
            cx(color_src[cell], color_dst[cell])

        # Step 2-5: per cell, compute/apply/uncompute
        # Ancilla layout: same[max_deg] + cnt[cw] + flag[1]
        with ancilla(max_deg + cw + 1) as scratch:
            same_wires = scratch.wires()[:max_deg]
            cnt_wires = scratch.wires()[max_deg:max_deg + cw]
            flag_wire = scratch.wires()[max_deg + cw]

            for cell in range(n):
                nbrs = neighbors[cell]
                die_start = cell * die_w
                die_wires = [dice[die_start + b] for b in range(die_w)]

                def _compute(cell=cell, nbrs=nbrs, die_wires=die_wires):
                    # same_wires[j] = both occupied and same color; inc cnt when set.
                    for j, nbr in enumerate(nbrs):
                        if j >= max_deg:
                            break
                        apply_pattern_x_wires(
                            [occ[cell], occ[nbr], color_src[cell], color_src[nbr]],
                            [1, 1, 1, 1],
                            same_wires[j],
                        )
                        apply_pattern_x_wires(
                            [occ[cell], occ[nbr], color_src[cell], color_src[nbr]],
                            [1, 1, 0, 0],
                            same_wires[j],
                        )
                        controlled_inc_wires(same_wires[j], cnt_wires)

                    # Occupied, cnt=k friendly neighbors, die<4-k: set flip flag.
                    max_k = min(len(nbrs), 4)
                    for friendly_count in range(max_k + 1):
                        threshold = 4 - friendly_count
                        if threshold <= 0:
                            continue
                        count_bits = int_to_bits(friendly_count, cw)
                        for die_value in range(threshold):
                            die_bits = int_to_bits(die_value, die_w)
                            all_controls = [occ[cell]] + cnt_wires + die_wires
                            all_pattern = [1] + count_bits + die_bits
                            apply_pattern_x_wires(all_controls, all_pattern, flag_wire)

                def _apply(cell=cell):
                    cx(flag_wire, color_dst[cell])

                compute(_compute)
                apply(_apply)
                uncompute()

    return sway_transition
