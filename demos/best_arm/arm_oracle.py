"""Arm-specific rollout oracles: fix the first-round black selector.

Each "arm" corresponds to a different first action in the Sway game.
The rollout oracle's sel_b1 register normally receives Hadamard gates
(uniform superposition over legal first moves).  An arm-specific oracle
fixes sel_b1 to a chosen action index, leaving the remaining randomness
(dice, opponent selectors) in superposition.

The oracle also provides a mark_oracle (Z on payoff qubit) for use
with coherent amplitude estimation.
"""

import math

from b01t import QReg, coherent, h, x, z, cx
from b01t.kit.arithmetic import binary_controlled_fan, int_to_bits

from demos.rollout.sway.sway_spec import SwaySpec
from demos.rollout.sway.sway_transition import make_sway_transition
from demos.rollout.sway.terminal_eval import make_terminal_eval
from b01t.zoo.rank_select import rank_select_binary


def make_arm_state_prep(spec: SwaySpec, action_index: int):
    """Create a @coherent state-preparation oracle for one arm.

    Identical to the standard rollout oracle except sel_b1 is set to
    *action_index* (via X gates) instead of being placed in superposition.
    All other randomness (dice, opponent selectors) remains in superposition.

    Args:
        spec: Sway game specification.
        action_index: which first move to fix (0-indexed among legal moves).
    """
    sway = make_sway_transition(spec)
    term = make_terminal_eval(spec)
    n = spec.n_cells
    H = spec.horizon
    sel_b1_width = spec.selector_width(spec.black_choices(1))

    @coherent
    def arm_state_prep(*regs: QReg):
        idx = 0

        occ = regs[idx]; idx += 1

        colors = []
        for _ in range(H + 1):
            colors.append(regs[idx]); idx += 1

        moves_b = []
        moves_w = []
        for _ in range(H):
            moves_b.append(regs[idx]); idx += 1
            moves_w.append(regs[idx]); idx += 1

        sels_b = []
        sels_w = []
        for _ in range(H):
            sels_b.append(regs[idx]); idx += 1
            sels_w.append(regs[idx]); idx += 1

        dice_regs = []
        for _ in range(H):
            dice_regs.append(regs[idx]); idx += 1

        payoff = regs[idx]; idx += 1

        # ---------- Prepare superpositions ----------
        for round_h in range(H):
            if round_h == 0:
                # First round black selector: FIX to action_index
                bits = int_to_bits(action_index, len(sels_b[0]))
                for i, b in enumerate(bits):
                    if b:
                        x(sels_b[0][i])
            else:
                for w in sels_b[round_h]:
                    h(w)
            for w in sels_w[round_h]:
                h(w)
            for w in dice_regs[round_h]:
                h(w)

        # ---------- Main loop ----------
        for round_h in range(H):
            color_in = colors[round_h]
            color_out = colors[round_h + 1]
            move_b = moves_b[round_h]
            move_w = moves_w[round_h]
            sel_b = sels_b[round_h]
            sel_w = sels_w[round_h]
            dice_h = dice_regs[round_h]

            # Black rank-select + apply
            rank_select_binary(occ, sel_b, move_b)
            binary_controlled_fan(move_b.wires(), occ.wires(), n)
            binary_controlled_fan(move_b.wires(), color_in.wires(), n)

            # White rank-select + apply
            rank_select_binary(occ, sel_w, move_w)
            binary_controlled_fan(move_w.wires(), occ.wires(), n)

            # Sway transition
            sway(occ, color_in, color_out, dice_h)

        # Terminal evaluation
        term(occ, colors[H], payoff)

    return arm_state_prep


def make_arm_mark_oracle(spec: SwaySpec):
    """Create a @coherent mark oracle: Z on the payoff qubit.

    This is shared across all arms since the payoff qubit is always
    the last register.
    """
    @coherent
    def mark_oracle(*regs: QReg):
        payoff = regs[-1]
        z(payoff[0])

    return mark_oracle
