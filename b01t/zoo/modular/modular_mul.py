"""In-place modular multiplication: |y> -> |ay mod N>.

Beauregard decomposition:
  1. Forward: acc <- a*y mod N  (schoolbook, controlled on bits of y)
  2. SWAP(y, acc)
  3. Inverse: acc <- acc - a^{-1}*y mod N  (cleans acc to |0>)

@primitive because the SWAP doesn't fit compute/apply/uncompute.
All gates are permutation gates.
"""

from b01t.core import QReg, Wire, primitive, cx, swap
from b01t.zoo.modular.modular_add import ctrl_modular_add_wires


def _modinv(a: int, N: int) -> int:
    """Modular inverse a^{-1} mod N via extended Euclidean algorithm."""
    if N == 1:
        return 0
    g, x, _ = _extended_gcd(a % N, N)
    if g != 1:
        raise ValueError(f"gcd({a}, {N}) = {g} != 1; no modular inverse")
    return x % N


def _extended_gcd(a: int, b: int) -> tuple[int, int, int]:
    if a == 0:
        return b, 0, 1
    g, x1, y1 = _extended_gcd(b % a, a)
    return g, y1 - (b // a) * x1, x1


def make_inplace_modular_mul(a_val: int, N: int):
    """Return a @primitive function for in-place: |y> -> |ay mod N>.

    Args:
        a_val: classical multiplier, must be coprime to N
        N:     classical modulus

    The returned function takes:
        y:       n-qubit register (transformed in-place)
        acc:     n-qubit ancilla accumulator (must start at |0>, restored)
        scratch: (n+2)-qubit ancilla (n const + 1 carry + 1 flag)
    """
    n = N.bit_length()
    a_inv = _modinv(a_val, N)

    @primitive
    def inplace_mul(y_reg: QReg, acc_reg: QReg, scratch: QReg):
        const_wires = scratch.wires()[:n]
        cin = scratch[n]
        flag = scratch[n + 1]
        y_w = y_reg.wires()
        acc_w = acc_reg.wires()

        # Forward: acc <- a*y mod N
        for i in range(n):
            addend = (a_val * (1 << i)) % N
            if addend == 0:
                continue
            ctrl_modular_add_wires(
                y_w[i], acc_w, addend, N, const_wires, cin, flag)

        # Swap y <-> acc
        for i in range(n):
            swap(y_w[i], acc_w[i])

        # Inverse: clean acc via a^{-1}
        # acc currently holds old y. We subtract a^{-1} * new_y from acc.
        # new_y = a * old_y mod N, so a^{-1} * new_y = old_y.
        # For each bit i of new_y: acc <- (acc - a_inv*2^i) mod N
        # Subtraction mod N: add (N - value) mod N.
        for i in range(n):
            sub_val = (N - (a_inv * (1 << i)) % N) % N
            if sub_val == 0:
                continue
            ctrl_modular_add_wires(
                y_w[i], acc_w, sub_val, N, const_wires, cin, flag)

    return inplace_mul
