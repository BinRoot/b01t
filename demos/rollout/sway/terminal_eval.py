"""Terminal payoff from the final board: set payoff qubit when black count exceeds white."""

from b01t import QReg, Wire, coherent, ancilla, compute, apply, uncompute, cx, x
from b01t.kit.arithmetic import apply_pattern_x_wires, int_to_bits
from .sway_spec import SwaySpec


def make_terminal_eval(spec: SwaySpec):
    """Create a @coherent terminal evaluation for the given spec."""
    cw = spec.count_width

    @coherent
    def terminal_eval(
        occ: QReg,
        color: QReg,
        payoff: QReg,
    ):
        """Compute payoff: black > white on the final board.

        1. Count black pieces into black_sum (compute)
        2. Count white pieces into white_sum (compute)
        3. Compare sums → flag (compute)
        4. Flip payoff from flag (apply)
        5. Uncompute sums and flag
        """
        n = len(occ)
        w = cw

        with ancilla(w + w + 1) as scratch:
            bs_wires = scratch.wires()[:w]
            ws_wires = scratch.wires()[w:w + w]
            flag_wire = scratch.wires()[w + w]

            def _compute():
                for cell in range(n):
                    for i in reversed(range(w)):
                        controls = [occ[cell], color[cell]] + bs_wires[:i]
                        apply_pattern_x_wires(controls, [1] * len(controls), bs_wires[i])

                    x(color[cell])
                    for i in reversed(range(w)):
                        controls = [occ[cell], color[cell]] + ws_wires[:i]
                        apply_pattern_x_wires(controls, [1] * len(controls), ws_wires[i])
                    x(color[cell])

                for b in range(1, n + 1):
                    for w_val in range(b):
                        b_bits = int_to_bits(b, w)
                        w_bits = int_to_bits(w_val, w)
                        controls = bs_wires + ws_wires
                        pattern = b_bits + w_bits
                        apply_pattern_x_wires(controls, pattern, flag_wire)

            def _apply():
                cx(flag_wire, payoff[0])

            compute(_compute)
            apply(_apply)
            uncompute()

    return terminal_eval
