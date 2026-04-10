"""One SIR transition step: infection, recovery, and state copy.

For each cell:
  1. Copy (inf, rem) from source to destination registers
  2. Count infected neighbors (compute)
  3. Infection: if S and die < threshold(k), flip inf_dst (compute + apply)
  4. Recovery: if I and die < gamma_threshold, flip inf_dst and rem_dst
  5. Uncompute neighbor count and flags
"""

from b01t import QReg, Wire, coherent, cx, x
from b01t.kit import ancilla, compute, apply, uncompute
from b01t.kit.arithmetic import (
    apply_pattern_x_wires,
    controlled_inc_wires,
    controlled_dec_wires,
    int_to_bits,
)
from .epidemic_spec import EpidemicSpec


def make_sir_transition(spec: EpidemicSpec):
    """Create a @coherent SIR transition for the given spec."""
    neighbors = spec.neighbors()
    die_w = spec.die_width
    cw = spec.cnt_width

    @coherent
    def sir_transition(
        inf_src: QReg,
        rem_src: QReg,
        inf_dst: QReg,
        rem_dst: QReg,
        dice: QReg,
    ):
        n = len(inf_src)

        # Step 1: copy state from src to dst
        for cell in range(n):
            cx(inf_src[cell], inf_dst[cell])
            cx(rem_src[cell], rem_dst[cell])

        # Step 2-5: per-cell infection and recovery
        # Ancilla: cnt[cw] + lt_flag[1] + event_flag[1]
        with ancilla(cw + 2) as scratch:
            cnt_wires = scratch.wires()[:cw]
            lt_flag = scratch.wires()[cw]
            event_flag = scratch.wires()[cw + 1]

            for cell in range(n):
                nbrs = neighbors[cell]
                die_start = cell * die_w
                die_wires = [dice[die_start + b] for b in range(die_w)]

                def _compute(cell=cell, nbrs=nbrs, die_wires=die_wires):
                    # Count infected neighbors
                    for nb in nbrs:
                        controlled_inc_wires(inf_src[nb], cnt_wires)

                    # Infection: S cell (inf=0, rem=0) with k infected neighbors
                    # and die < infection_threshold(k) → set event_flag
                    for k in range(len(nbrs) + 1):
                        threshold = spec.infection_threshold(k)
                        if threshold <= 0:
                            continue
                        count_bits = int_to_bits(k, cw)
                        for die_value in range(threshold):
                            die_bits = int_to_bits(die_value, die_w)
                            # S = inf=0, rem=0; match count=k and die<threshold
                            controls = ([inf_src[cell], rem_src[cell]]
                                       + cnt_wires + die_wires)
                            pattern = [0, 0] + count_bits + die_bits
                            apply_pattern_x_wires(controls, pattern, event_flag)

                    # Recovery: I cell (inf=1, rem=0) with die < recovery_threshold
                    rec_threshold = spec.recovery_threshold()
                    if rec_threshold > 0:
                        for die_value in range(rec_threshold):
                            die_bits = int_to_bits(die_value, die_w)
                            controls = ([inf_src[cell], rem_src[cell]]
                                       + die_wires)
                            pattern = [1, 0] + die_bits
                            apply_pattern_x_wires(controls, pattern, lt_flag)

                def _apply(cell=cell):
                    # Infection: flip inf_dst
                    cx(event_flag, inf_dst[cell])
                    # Recovery: flip both inf_dst and rem_dst
                    cx(lt_flag, inf_dst[cell])
                    cx(lt_flag, rem_dst[cell])

                compute(_compute)
                apply(_apply)
                uncompute()

    return sir_transition
