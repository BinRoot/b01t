"""Bernstein-Vazirani algorithm: recover s from f(x) = s*x with one query.

H on all inputs, prepare |-> on target, query, H on all inputs, measure.
The measurement outcome is the hidden string s.
"""

from typing import Sequence

from b01t import QReg, adaptive, h, x, cx, measure_all


def make_bv_algorithm(secret: Sequence[int]):
    """Return an @adaptive program that runs BV for the given hidden string."""
    s = tuple(secret)
    n = len(s)

    @adaptive
    def algorithm(inp: QReg, tgt: QReg):
        # Hadamard on all inputs
        for i in range(n):
            h(inp[i])
        # Prepare |-> on target
        x(tgt[0])
        h(tgt[0])
        # Oracle: CX for each s_i = 1
        for i in range(n):
            if s[i] == 1:
                cx(inp[i], tgt[0])
        # Hadamard on all inputs
        for i in range(n):
            h(inp[i])
        # Measure: outcome = s
        return measure_all(inp)

    return algorithm
