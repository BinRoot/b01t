"""Phase oracle: flips the phase of marked basis states via ancilla discipline."""

from typing import Sequence

from b01t.core import QReg, coherent, mcx, x, z
from b01t.kit import ancilla, compute, phase, uncompute


def make_phase_oracle(marked_bits: Sequence[int]):
    """Return a @coherent oracle that flips the phase of |marked_bits>.

    marked_bits: sequence of 0s and 1s, one per qubit.

    For 1-qubit: Z directly (no ancilla). XZX for marked=0.
    For 2+ qubits: MCX into ancilla, Z phase kick, uncompute.
    """
    bits = tuple(marked_bits)
    n = len(bits)
    if n < 1:
        raise ValueError("marked_bits must have at least one element")
    if not all(b in (0, 1) for b in bits):
        raise ValueError("marked_bits entries must be 0 or 1")

    @coherent
    def oracle(sys: QReg):
        if n == 1:
            if bits[0] == 0:
                x(sys[0])
            z(sys[0])
            if bits[0] == 0:
                x(sys[0])
            return

        with ancilla(1) as anc:
            def _compute():
                for i in range(n):
                    if bits[i] == 0:
                        x(sys[i])
                mcx(sys.wires(), anc[0])

            compute(_compute)
            phase(lambda: z(anc[0]))
            uncompute()

    return oracle


# Convenience: the original 2-qubit |11> oracle.
phase_oracle = make_phase_oracle([1, 1])
