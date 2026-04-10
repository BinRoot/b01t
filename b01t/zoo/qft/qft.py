"""Quantum Fourier Transform (QFT) and inverse QFT.

The QFT maps computational basis states to the Fourier basis:
  QFT|j> = (1/sqrt(2^n)) sum_k exp(2*pi*i*j*k/2^n) |k>

The circuit processes qubits from LSB to MSB without a final bit-reversal
swap.  This matches the QPE convention where ``counting[k]`` controls
``U^{2^k}``, so the IQFT can decode the phase without additional
permutations.

The controlled-phase gate CP(theta) = diag(1,1,1,e^{i*theta}) is
decomposed as CRZ(theta) + Rz(theta/2) on the control qubit (the
two differ by a phase on the control that must be compensated).

@parametric because CRZ and Rz are continuous rotations.
"""

import math

from b01t.core import QReg, parametric, h, crz, rz, swap


def _cp(theta: float, ctrl, tgt) -> None:
    """Controlled-phase gate: diag(1, 1, 1, e^{i*theta}).

    Decomposed as CRZ(theta, ctrl, tgt) followed by Rz(theta/2, ctrl).
    """
    crz(theta, ctrl, tgt)
    rz(theta / 2, ctrl)


@parametric
def qft(reg: QReg):
    """Quantum Fourier Transform on register reg."""
    n = len(reg)
    for j in range(n):
        h(reg[j])
        for k in range(j + 1, n):
            angle = math.pi / (1 << (k - j))
            _cp(angle, reg[k], reg[j])


@parametric
def inverse_qft(reg: QReg):
    """Inverse QFT: adjoint of QFT."""
    n = len(reg)
    for j in range(n - 1, -1, -1):
        for k in range(n - 1, j, -1):
            angle = -math.pi / (1 << (k - j))
            _cp(angle, reg[k], reg[j])
        h(reg[j])
