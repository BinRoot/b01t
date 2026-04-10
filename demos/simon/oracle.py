"""Simon oracle: 2-to-1 function with hidden XOR-mask s.

Implements f(x) = x if x < x XOR s, else f(x) = x XOR s.
This ensures f(x) = f(x XOR s) for all x.

Circuit: copy input to output register, then conditionally XOR the mask.
The conditional is: if the first bit where s_i=1 is set in x, XOR s
into the output. This makes the function 2-to-1 with period s.

All gates are permutation gates (cx, x), so no ancilla discipline is needed
since the oracle operates system-to-system.
"""

from typing import Sequence

from b01t import QReg, coherent, cx, x


def make_simon_oracle(secret: Sequence[int]):
    """Return a @coherent oracle for hidden string s.

    secret: sequence of 0s and 1s. Must have at least one 1
            (s=0 is the trivial 1-to-1 case).

    Registers: inp (n qubits), out (n qubits).
    Maps |x, 0> -> |x, f(x)> where f(x) = f(x XOR s).
    """
    s = tuple(secret)
    n = len(s)
    if n < 1:
        raise ValueError("secret must have at least one element")
    if not all(b in (0, 1) for b in s):
        raise ValueError("secret entries must be 0 or 1")

    # Find the first index where s_i = 1 (the "pivot")
    pivot = None
    for i in range(n):
        if s[i] == 1:
            pivot = i
            break

    @coherent
    def oracle(inp: QReg, out: QReg):
        # Step 1: copy input to output (out = x)
        for i in range(n):
            cx(inp[i], out[i])
        # Step 2: if s != 0, conditionally XOR s into output
        # Condition: inp[pivot] is set → XOR s into out
        if pivot is not None:
            for i in range(n):
                if s[i] == 1 and i != pivot:
                    cx(inp[pivot], out[i])
            # Flip the pivot bit in output (effectively: out[pivot] ^= inp[pivot])
            # Combined with the copy, this gives out[pivot] = 0 when inp[pivot]=1
            # which makes f(x) = f(x XOR s)
            cx(inp[pivot], out[pivot])

    return oracle
