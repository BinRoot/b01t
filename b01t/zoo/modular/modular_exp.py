"""Controlled modular exponentiation for Shor's algorithm.

For each counting register bit k:
  if ctrl[k]=|1>: y <- y * a^(2^k) mod N

Uses doubly-controlled modular additions: the Toffoli of (ctrl[k], y[i])
is computed into a temp wire, which then controls the modular add.

@primitive because SWAP doesn't fit compute/apply/uncompute.
All gates are permutation gates (x, cx, ccx, mcx, swap).
"""

from b01t.core import QReg, primitive, cx, ccx
from b01t.zoo.modular.modular_add import ctrl_modular_add_wires
from b01t.zoo.modular.modular_mul import _modinv


def make_controlled_modular_exp(a_val: int, N: int, num_ctrl_bits: int):
    """Return a @primitive controlled modular exponentiation oracle.

    Implements the sequence of controlled-U^(2^k) for QPE/Shor.

    Args:
        a_val:         base, coprime to N
        N:             modulus
        num_ctrl_bits: number of counting (control) qubits

    The returned function takes:
        ctrl:    counting register (num_ctrl_bits qubits)
        y:       work register (n qubits, start at |1>)
        acc:     accumulator ancilla (n qubits, start at |0>)
        scratch: (n+3)-qubit ancilla (n const + 1 carry + 1 flag + 1 temp)
    """
    n = N.bit_length()

    # Precompute a^(2^k) mod N and their inverses
    powers = []
    power = a_val % N
    for k in range(num_ctrl_bits):
        powers.append(power)
        power = (power * power) % N

    @primitive
    def controlled_modular_exp(
        ctrl: QReg, y_reg: QReg, acc: QReg, scratch: QReg,
    ):
        from b01t.core import swap

        s = scratch.wires()
        const_wires = s[:n]
        cin = s[n]
        flag = s[n + 1]
        temp = s[n + 2]
        y_w = y_reg.wires()
        acc_w = acc.wires()

        for k in range(num_ctrl_bits):
            a_k = powers[k]
            a_k_inv = _modinv(a_k, N)

            # Forward: acc <- a_k * y mod N
            # Double control: ctrl[k] AND y[i] → temp → modular add
            for i in range(n):
                addend = (a_k * (1 << i)) % N
                if addend == 0:
                    continue
                ccx(ctrl[k], y_w[i], temp)
                ctrl_modular_add_wires(
                    temp, acc_w, addend, N, const_wires, cin, flag)
                ccx(ctrl[k], y_w[i], temp)

            # Controlled SWAP (Fredkin gate per wire pair)
            for i in range(n):
                cx(acc_w[i], y_w[i])
                ccx(ctrl[k], y_w[i], acc_w[i])
                cx(acc_w[i], y_w[i])

            # Inverse: clean acc using a_k^{-1}
            # Double control: ctrl[k] AND new_y[i]
            for i in range(n):
                sub_val = (N - (a_k_inv * (1 << i)) % N) % N
                if sub_val == 0:
                    continue
                ccx(ctrl[k], y_w[i], temp)
                ctrl_modular_add_wires(
                    temp, acc_w, sub_val, N, const_wires, cin, flag)
                ccx(ctrl[k], y_w[i], temp)

    return controlled_modular_exp
