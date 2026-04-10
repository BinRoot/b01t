"""Deutsch's algorithm: determine if f is constant or balanced with one query.

Prepares |+> on input and |-> on target (phase kickback register),
queries the oracle once, then measures the input qubit.
Result: 0 = constant, 1 = balanced.
"""

from b01t import QReg, adaptive, h, x, cx, measure


def make_deutsch_algorithm(f0: int, f1: int):
    """Return an @adaptive program that runs Deutsch's algorithm for f(0)=f0, f(1)=f1.

    The oracle gates are inlined into the adaptive circuit (the @coherent
    oracle in oracle.py is for standalone certification/verification).
    """

    @adaptive
    def algorithm(inp: QReg, tgt: QReg):
        # Prepare |+> on input
        h(inp[0])
        # Prepare |-> on target (phase kickback)
        x(tgt[0])
        h(tgt[0])
        # Oracle U_f: |x, y> -> |x, y XOR f(x)>
        if f0 == 1:
            x(tgt[0])
        if f0 != f1:
            cx(inp[0], tgt[0])
        # Interfere
        h(inp[0])
        # Measure: 0 = constant, 1 = balanced
        return measure(inp[0])

    return algorithm
