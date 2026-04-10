"""Terminal payoff: set payoff qubit when final #infected <= threshold T."""

from b01t import QReg, coherent, cx
from b01t.kit import ancilla, compute, apply, uncompute
from b01t.kit.arithmetic import (
    apply_pattern_x_wires,
    controlled_inc_wires,
    int_to_bits,
)
from .epidemic_spec import EpidemicSpec


def make_epidemic_terminal_eval(spec: EpidemicSpec):
    """Create a @coherent terminal evaluation for the epidemic model.

    Counts final infected population, sets payoff=1 if count <= threshold T.
    Uses compute/apply/uncompute: the compute block counts infected and
    sets a flag wire, the apply block copies the flag to payoff.
    """
    cw = spec.count_width
    T = spec.threshold

    @coherent
    def epidemic_terminal_eval(
        inf: QReg,
        payoff: QReg,
    ):
        n = len(inf)

        # Ancilla: count register (cw bits) + flag (1 bit)
        with ancilla(cw + 1) as scratch:
            count_wires = scratch.wires()[:cw]
            flag_wire = scratch.wires()[cw]

            def _compute():
                # Count infected cells
                for cell in range(n):
                    controlled_inc_wires(inf[cell], count_wires)
                # Set flag = 1 iff count <= T
                for v in range(T + 1):
                    bits = int_to_bits(v, cw)
                    apply_pattern_x_wires(count_wires, bits, flag_wire)

            def _apply():
                cx(flag_wire, payoff[0])

            compute(_compute)
            apply(_apply)
            uncompute()

    return epidemic_terminal_eval
