"""@coherent Sway rollout oracle for H rounds."""

from b01t import QReg, coherent, cx, h, x
from b01t.kit.arithmetic import binary_controlled_fan

from .sway_spec import SwaySpec
from b01t.zoo.rank_select import rank_select_binary
from .sway_transition import make_sway_transition
from .terminal_eval import make_terminal_eval


def make_rollout_oracle(spec: SwaySpec, prepare_superpositions: bool = True):
    """Create a @coherent rollout oracle for the given spec.

    prepare_superpositions: when True (default), the oracle is the full
    unitary U_O of the paper, with selector and dice registers prepared
    in uniform superposition. When False, the H-prep is omitted and the
    circuit is a pure permutation on basis states; selector and dice
    values must be supplied as classical input bits. Used by the
    Monte-Carlo and branch-agreement harnesses to sample one branch.
    """
    sway = make_sway_transition(spec)
    term = make_terminal_eval(spec)
    n = spec.n_cells
    H = spec.horizon
    move_w = len(int_to_bits(n - 1, 0)) if n <= 1 else max(1, int(__import__('math').ceil(__import__('math').log2(n))))

    @coherent
    def rollout_oracle(*regs: QReg):
        """Multi-round rollout oracle for Sway.

        Register order must match SwaySpec.register_specs().
        Move registers are binary-encoded (ceil(log2(N)) bits).
        """
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

        # Prepare superpositions
        if prepare_superpositions:
            for round_h in range(H):
                for w in sels_b[round_h]:
                    h(w)
                for w in sels_w[round_h]:
                    h(w)
                for w in dice_regs[round_h]:
                    h(w)

        # Main loop: H rounds
        for round_h in range(H):
            color_in = colors[round_h]
            color_out = colors[round_h + 1]
            move_b = moves_b[round_h]
            move_w = moves_w[round_h]
            sel_b = sels_b[round_h]
            sel_w = sels_w[round_h]
            dice_h = dice_regs[round_h]
            mw = len(move_b)

            # 1. Black rank-select (binary index)
            rank_select_binary(occ, sel_b, move_b)

            # 2. Apply black move: decode binary index, set occ + color=1
            binary_controlled_fan(move_b.wires(), occ.wires(), n)
            binary_controlled_fan(move_b.wires(), color_in.wires(), n)

            # 3. White rank-select (binary index)
            rank_select_binary(occ, sel_w, move_w)

            # 4. Apply white move: decode binary index, set occ only
            binary_controlled_fan(move_w.wires(), occ.wires(), n)

            # 5. Sway transition
            sway(occ, color_in, color_out, dice_h)

        # Terminal evaluation
        term(occ, colors[H], payoff)

    return rollout_oracle
