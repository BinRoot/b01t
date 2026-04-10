"""Deutsch oracle: U_f |x, y> = |x, y XOR f(x)> for f: {0,1} -> {0,1}.

Four possible oracles, all using only permutation gates (x, cx):

  f(0)=0, f(1)=0  (constant)  -> identity
  f(0)=1, f(1)=1  (constant)  -> X on target
  f(0)=0, f(1)=1  (balanced)  -> CX(input, target)
  f(0)=1, f(1)=0  (balanced)  -> X on target + CX(input, target)
"""

from b01t import QReg, coherent, cx, x


def make_deutsch_oracle(f0: int, f1: int):
    """Return a @coherent oracle implementing f(0)=f0, f(1)=f1.

    The oracle maps |x, y> -> |x, y XOR f(x)> using only permutation
    gates (X, CX), so it is safe by construction with no ancilla needed.
    """
    if f0 not in (0, 1) or f1 not in (0, 1):
        raise ValueError("f0 and f1 must be 0 or 1")

    @coherent
    def oracle(inp: QReg, tgt: QReg):
        if f0 == 1:
            x(tgt[0])
        if f0 != f1:
            cx(inp[0], tgt[0])

    return oracle
