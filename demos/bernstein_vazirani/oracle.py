"""Bernstein-Vazirani oracle: U_f |x, y> = |x, y XOR (s*x)>.

The inner product s*x = s_0*x_0 XOR s_1*x_1 XOR ... XOR s_{n-1}*x_{n-1}.
Implemented as CX(x_i, target) for each i where s_i = 1.
All gates are permutation gates (cx).
"""

from typing import Sequence

from b01t import QReg, coherent, cx


def make_bv_oracle(secret: Sequence[int]):
    """Return a @coherent oracle for the hidden string secret.

    secret: sequence of 0s and 1s, one per input qubit.
    """
    s = tuple(secret)
    n = len(s)
    if n < 1:
        raise ValueError("secret must have at least one element")
    if not all(b in (0, 1) for b in s):
        raise ValueError("secret entries must be 0 or 1")

    @coherent
    def oracle(inp: QReg, tgt: QReg):
        for i in range(n):
            if s[i] == 1:
                cx(inp[i], tgt[0])

    return oracle
