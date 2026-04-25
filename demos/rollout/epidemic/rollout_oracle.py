"""@coherent epidemic rollout oracle for H rounds.

Each round:
  1. Copy previous state to working registers (or set initial conditions)
  2. Compute occupancy (occ = inf OR rem), rank-select vaccination target
  3. Vaccinate: set rem_work=1 for selected susceptible cell
  4. SIR transition: (inf_work, rem_work) -> (inf_h, rem_h)
  5. Undo vaccination, occ, and copy on working registers

Terminal evaluation: payoff=1 if final #infected <= threshold T.
"""

from b01t import QReg, coherent, h, x, cx
from b01t.kit.arithmetic import binary_controlled_fan

from .epidemic_spec import EpidemicSpec
from b01t.zoo.rank_select import rank_select_binary
from .sir_transition import make_sir_transition
from .terminal_eval import make_epidemic_terminal_eval


def make_epidemic_rollout_oracle(spec: EpidemicSpec, prepare_superpositions: bool = True):
    """Create a @coherent rollout oracle for the epidemic model.

    prepare_superpositions: when True (default), the oracle is the full
    unitary U_O of the paper, with selector and dice registers prepared
    in uniform superposition. When False, the H-prep is omitted and the
    circuit is a pure permutation on basis states; selector and dice
    values must be supplied as classical input bits.
    """
    sir = make_sir_transition(spec)
    term = make_epidemic_terminal_eval(spec)
    n = spec.n_cells
    H = spec.horizon

    @coherent
    def epidemic_rollout_oracle(*regs: QReg):
        """Register order matches EpidemicSpec.register_specs()."""
        idx = 0

        # Working registers
        inf_work = regs[idx]; idx += 1
        rem_work = regs[idx]; idx += 1
        occ_work = regs[idx]; idx += 1

        # Per-round output
        inf_out = []
        rem_out = []
        for _ in range(H):
            inf_out.append(regs[idx]); idx += 1
            rem_out.append(regs[idx]); idx += 1

        # Per-round move registers
        move_regs = []
        for _ in range(H):
            move_regs.append(regs[idx]); idx += 1

        # Selector registers
        sel_regs = []
        for h_round in range(H):
            choices = spec.n_susceptible_initially if h_round == 0 else n
            sw = spec.selector_width(choices)
            if sw > 0:
                sel_regs.append(regs[idx]); idx += 1
            else:
                sel_regs.append(None)

        # Dice registers
        dice_regs = []
        for _ in range(H):
            dice_regs.append(regs[idx]); idx += 1

        payoff = regs[idx]; idx += 1

        # ── Prepare superpositions ──
        if prepare_superpositions:
            for h_round in range(H):
                if sel_regs[h_round] is not None:
                    for w in sel_regs[h_round]:
                        h(w)
                for w in dice_regs[h_round]:
                    h(w)

        # ── Main loop ──
        for h_round in range(H):
            inf_h = inf_out[h_round]
            rem_h = rem_out[h_round]
            move = move_regs[h_round]
            sel = sel_regs[h_round]
            dice = dice_regs[h_round]

            # 1. Copy previous state to working registers
            if h_round == 0:
                for i in spec.initial_infected:
                    x(inf_work[i])
            else:
                for i in range(n):
                    cx(inf_out[h_round - 1][i], inf_work[i])
                    cx(rem_out[h_round - 1][i], rem_work[i])

            # 2. Compute occupancy mask: occ = inf OR rem
            for i in range(n):
                cx(inf_work[i], occ_work[i])
                cx(rem_work[i], occ_work[i])

            # 3. Rank-select vaccination target
            if sel is not None:
                rank_select_binary(occ_work, sel, move)

            # 4. Apply vaccination: decode move index, flip rem_work
            binary_controlled_fan(move.wires(), [rem_work[i] for i in range(n)], n)

            # 5. SIR transition
            sir(inf_work, rem_work, inf_h, rem_h, dice)

            # 6. Undo vaccination
            binary_controlled_fan(move.wires(), [rem_work[i] for i in range(n)], n)

            # 7. Undo rank-select
            if sel is not None:
                rank_select_binary(occ_work, sel, move)

            # 8. Undo occupancy mask
            for i in range(n):
                cx(rem_work[i], occ_work[i])
                cx(inf_work[i], occ_work[i])

            # 9. Uncopy working registers
            if h_round == 0:
                for i in spec.initial_infected:
                    x(inf_work[i])
            else:
                for i in range(n):
                    cx(rem_out[h_round - 1][i], rem_work[i])
                    cx(inf_out[h_round - 1][i], inf_work[i])

        # ── Terminal evaluation ──
        final_inf = inf_out[H - 1]
        term(final_inf, payoff)

    return epidemic_rollout_oracle
