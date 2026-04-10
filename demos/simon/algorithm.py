"""Simon's algorithm: recover hidden XOR-mask s with O(n) quantum queries.

Each run produces a random y such that y*s = 0 (mod 2).
After n-1 linearly independent samples, s is recovered via
Gaussian elimination (classical post-processing, not part of the circuit).
"""

from typing import Sequence

from b01t import QReg, adaptive, h, cx, x, measure_all


def make_simon_algorithm(secret: Sequence[int]):
    """Return an @adaptive program for one round of Simon's algorithm.

    One round: H on input, query oracle, H on input, measure input.
    The measurement outcome y satisfies y*s = 0 (mod 2).
    """
    s = tuple(secret)
    n = len(s)

    pivot = None
    for i in range(n):
        if s[i] == 1:
            pivot = i
            break

    @adaptive
    def algorithm(inp: QReg, out: QReg):
        # Hadamard on input
        for i in range(n):
            h(inp[i])
        # Oracle (inlined)
        for i in range(n):
            cx(inp[i], out[i])
        if pivot is not None:
            for i in range(n):
                if s[i] == 1 and i != pivot:
                    cx(inp[pivot], out[i])
            cx(inp[pivot], out[pivot])
        # Hadamard on input
        for i in range(n):
            h(inp[i])
        # Measure input register
        return measure_all(inp)

    return algorithm
