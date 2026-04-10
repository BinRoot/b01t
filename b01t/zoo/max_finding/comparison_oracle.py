"""Comparison oracle for Durr-Hoyer: AE + threshold comparison + phase flip.

Given a coherent amplitude estimation circuit, this module builds a
@parametric oracle that:

1. Runs coherent AE -> theta estimate in counting register
2. Loads a classical threshold into a register
3. Compares: flag = (threshold < estimate), i.e. arm beats threshold
4. Phase-flips the flag
5. Uncomputes comparison, threshold, and AE

The oracle can be used as the marking oracle inside Grover search
over arm indices.
"""

from typing import Callable

from b01t.core import QReg, parametric
from b01t.core.builder import DSLFunction, adjoint as broad_adjoint
from b01t.core.gates import x, z
from b01t.kit.arithmetic.primitives import int_to_bits
from b01t.kit.arithmetic.comparator import less_than
from b01t.kit.controlled import inline_exact


def _load_threshold(reg: QReg, value: int) -> None:
    """Load a classical integer into a register via X gates (self-inverse)."""
    bits = int_to_bits(value, len(reg))
    for i, b in enumerate(bits):
        if b:
            x(reg[i])


def make_comparison_oracle(
    ae_fn: DSLFunction,
    threshold_value: int,
    precision: int,
):
    """Build a @parametric comparison oracle for Durr-Hoyer Grover search.

    Args:
        ae_fn: ``@parametric`` coherent AE from ``make_coherent_ae``.
               Takes ``(counting: QReg, *work_regs: QReg)``.
        threshold_value: classical threshold (integer encoding of the
                         QPE angle estimate to beat).
        precision: bit-width of counting / threshold registers.

    Returns:
        A ``@parametric`` function
        ``(*work_regs, ae_counting, thresh_reg, cmp_flag)`` that
        phase-flips states whose AE estimate exceeds the threshold.
        All auxiliary registers are restored after the call.

    Convention: the last three registers are always
    ``(ae_counting, thresh_reg, cmp_flag)``.  Everything before them
    is passed through to the AE as work registers.
    """

    @parametric
    def comparison_oracle(*regs: QReg):
        # Last 3 regs are ae_counting, thresh_reg, cmp_flag.
        # Everything before is work registers for AE.
        cmp_flag = regs[-1]
        thresh_reg = regs[-2]
        ae_counting = regs[-3]
        work_regs = regs[:-3]

        # --- Forward: compute AE estimate ---
        ae_fn(ae_counting, *work_regs)

        # --- Load classical threshold ---
        _load_threshold(thresh_reg, threshold_value)

        # --- Compare: flag = (threshold < estimate) ---
        # less_than uses the CMA apply() pattern, which the broad path
        # doesn't support.  inline_exact captures the exact ops and
        # re-emits them as flat broad-path gates.
        inline_exact(less_than, thresh_reg, ae_counting, cmp_flag)

        # --- Phase flip ---
        z(cmp_flag[0])

        # --- Uncompute comparison (less_than is self-inverse for result) ---
        inline_exact(less_than, thresh_reg, ae_counting, cmp_flag)

        # --- Unload threshold ---
        _load_threshold(thresh_reg, threshold_value)

        # --- Uncompute AE ---
        broad_adjoint(ae_fn, ae_counting, *work_regs)

    return comparison_oracle
