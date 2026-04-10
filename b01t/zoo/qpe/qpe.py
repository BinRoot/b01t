"""Quantum Phase Estimation (QPE).

Given a unitary U with eigenvector |psi> and eigenvalue e^(2*pi*i*theta),
QPE estimates theta using t counting qubits to t bits of precision.

Circuit:
  1. H on all counting qubits
  2. Controlled-U^(2^k) for each counting qubit k
  3. Inverse QFT on counting register

The oracle function must implement the controlled-U^(2^k) operations
on the work register, controlled by the counting register bits.

@parametric because inverse QFT uses continuous rotations.
"""

from typing import Callable

from b01t.core import QReg, parametric, h
from b01t.zoo.qft import inverse_qft


def make_qpe(oracle_fn: Callable):
    """Return a @parametric QPE circuit.

    The oracle_fn must be a callable that takes (counting_reg, work_reg, ...)
    and applies controlled-U^(2^k) for each counting bit k.
    Additional registers (acc, scratch) are passed through.

    Args:
        oracle_fn: function(ctrl, work, *extra_regs) that applies the
                   controlled unitary operations

    The returned function takes:
        counting: t-qubit counting register
        work:     work register (should be in eigenstate |psi> of U)
        *extra:   additional registers passed to oracle_fn
    """

    @parametric
    def qpe(counting: QReg, work: QReg, *extra_regs: QReg):
        # Step 1: superposition on counting register
        for i in range(len(counting)):
            h(counting[i])

        # Step 2: controlled-U^(2^k) via the oracle
        oracle_fn(counting, work, *extra_regs)

        # Step 3: inverse QFT on counting register
        inverse_qft(counting)

    return qpe
