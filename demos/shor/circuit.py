"""Shor's order-finding circuit: QPE with modular exponentiation oracle.

The circuit:
  1. Initialize work register to |1>
  2. Run QPE with controlled modular exponentiation
  3. Measure counting register

The measurement outcome encodes the period r of a^r = 1 (mod N),
which is extracted classically via continued fractions.

@adaptive because it measures. The oracle is inlined as @parametric
(the @primitive zoo version can't be called from @adaptive).
"""

from b01t import QReg, adaptive, parametric, x, h, cx, ccx, swap, measure_all
from b01t.zoo.qft import inverse_qft
from b01t.zoo.modular.modular_add import ctrl_modular_add_wires
from b01t.zoo.modular.modular_mul import _modinv


def _make_parametric_modular_exp(a_val: int, N: int, num_ctrl_bits: int):
    """Build a @parametric modular exponentiation for use inside @adaptive.

    Same logic as zoo/modular/modular_exp but through the broad IR path.
    """
    n = N.bit_length()

    powers = []
    power = a_val % N
    for k in range(num_ctrl_bits):
        powers.append(power)
        power = (power * power) % N

    @parametric
    def modular_exp(ctrl: QReg, y_reg: QReg, acc: QReg, scratch: QReg):
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

            # Forward: acc <- a_k * y mod N (doubly controlled)
            for i in range(n):
                addend = (a_k * (1 << i)) % N
                if addend == 0:
                    continue
                ccx(ctrl[k], y_w[i], temp)
                ctrl_modular_add_wires(
                    temp, acc_w, addend, N, const_wires, cin, flag)
                ccx(ctrl[k], y_w[i], temp)

            # Controlled SWAP (Fredkin per wire)
            for i in range(n):
                cx(acc_w[i], y_w[i])
                ccx(ctrl[k], y_w[i], acc_w[i])
                cx(acc_w[i], y_w[i])

            # Inverse: clean acc
            for i in range(n):
                sub_val = (N - (a_k_inv * (1 << i)) % N) % N
                if sub_val == 0:
                    continue
                ccx(ctrl[k], y_w[i], temp)
                ctrl_modular_add_wires(
                    temp, acc_w, sub_val, N, const_wires, cin, flag)
                ccx(ctrl[k], y_w[i], temp)

    return modular_exp


def make_shor_circuit(a_val: int, N: int, num_counting_bits: int):
    """Return an @adaptive Shor order-finding circuit.

    Args:
        a_val:             base for order finding, coprime to N
        N:                 number to factor (or find order modulo)
        num_counting_bits: precision bits (typically 2*n where n = N.bit_length())

    The returned function takes:
        counting: num_counting_bits-qubit register (measured at end)
        y:        n-qubit work register
        acc:      n-qubit accumulator ancilla
        scratch:  (n+3)-qubit scratch ancilla
    """
    oracle = _make_parametric_modular_exp(a_val, N, num_counting_bits)

    @adaptive
    def shor_circuit(counting: QReg, y_reg: QReg, acc: QReg, scratch: QReg):
        # Initialize work register to |1>
        x(y_reg[0])

        # Hadamard on counting register
        for i in range(len(counting)):
            h(counting[i])

        # Controlled modular exponentiation
        oracle(counting, y_reg, acc, scratch)

        # Inverse QFT on counting register
        inverse_qft(counting)

        # Measure counting register
        return measure_all(counting)

    return shor_circuit
