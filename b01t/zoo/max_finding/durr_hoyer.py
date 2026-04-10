"""Durr-Hoyer quantum maximum finding.

Classical outer loop with quantum inner search.  Each iteration builds
a Grover search circuit whose marking oracle uses coherent amplitude
estimation to compare arms against a threshold.

Architecture::

    Classical loop (O(sqrt(k)) iterations):
      threshold <- current best estimate
      Build Grover search circuit:
        arm_index in superposition
        marking oracle = comparison_oracle(threshold)
        diffusion on arm_index
      Measure arm_index -> candidate arm
      Update threshold if candidate is better

The inner search circuit is fully coherent (no mid-circuit measurement).
The outer loop is classical: threshold updates happen between circuits.
"""

import math
from dataclasses import dataclass
from typing import Callable

from b01t.core import QReg, parametric
from b01t.core.builder import DSLFunction
from b01t.core.gates import h, x, z, cz, mcx
from b01t.zoo.qae import make_coherent_ae
from .comparison_oracle import make_comparison_oracle


def _diffusion_on_register(reg: QReg) -> None:
    """Grover diffusion (2|0><0| - I) on a register.

    Emits gates directly into the current @parametric context.
    """
    n = len(reg)
    for w in reg:
        x(w)
    if n == 1:
        z(reg[0])
    elif n == 2:
        cz(reg[0], reg[1])
    else:
        h(reg[-1])
        mcx(reg.wires()[:-1], reg[-1])
        h(reg[-1])
    for w in reg:
        x(w)


def make_search_step(
    comparison_oracle_fn: DSLFunction,
    arm_index_width: int,
):
    """Build one Grover iteration: oracle + diffusion on arm_index.

    Args:
        comparison_oracle_fn: ``@parametric`` comparison oracle from
            ``make_comparison_oracle``.  Takes
            ``(*work_regs, ae_counting, thresh_reg, cmp_flag)``.
        arm_index_width: number of qubits in the arm_index register.

    Returns:
        A ``@parametric`` function taking
        ``(arm_index, *work_regs, ae_counting, thresh_reg, cmp_flag)``.
    """

    @parametric
    def grover_step(*regs: QReg):
        arm_index = regs[0]
        oracle_regs = regs[1:]  # work_regs + ae_counting + thresh + flag

        # Oracle: mark arms that beat the threshold
        comparison_oracle_fn(*oracle_regs)

        # Diffusion about the uniform superposition over arm indices
        for w in arm_index:
            h(w)
        _diffusion_on_register(arm_index)
        for w in arm_index:
            h(w)

    return grover_step


@dataclass
class DurrHoyerRunner:
    """Classical controller for Durr-Hoyer quantum maximum finding.

    Each arm is specified by a ``state_prep`` (``@coherent``)
    and a ``mark_oracle`` (``@coherent``).  The runner builds
    coherent AE for each arm, then iterates the classical loop.

    Attributes:
        arm_state_preps: list of @coherent state_prep functions.
        arm_mark_oracles: list of @coherent mark_oracle functions.
        ae_precision: number of QPE precision bits.
        work_reg_specs: list of (name, size) specs for work registers.
        seed: random seed for the initial arm choice.
    """
    arm_state_preps: list
    arm_mark_oracles: list
    ae_precision: int
    work_reg_specs: list
    seed: int = 42

    def __post_init__(self):
        k = len(self.arm_state_preps)
        if k != len(self.arm_mark_oracles):
            raise ValueError("state_preps and mark_oracles must have the same length")
        if k < 2:
            raise ValueError("need at least 2 arms")
        self.num_arms = k
        self.arm_index_width = max(1, math.ceil(math.log2(k)))

        # Pre-build coherent AE for each arm.
        self.arm_aes: list[DSLFunction] = []
        for prep, oracle in zip(self.arm_state_preps, self.arm_mark_oracles):
            ae = make_coherent_ae(prep, oracle)
            self.arm_aes.append(ae)

    def build_search_circuit(
        self,
        threshold: int,
        arm_index: int,
        num_grover_iters: int = 1,
    ) -> DSLFunction:
        """Build one search iteration's circuit for a specific arm.

        This builds the comparison oracle for the given arm and
        returns a ``@parametric`` circuit that can be compiled to
        Qiskit for structural verification.

        Args:
            threshold: current threshold (integer QPE angle encoding).
            arm_index: which arm to evaluate.
            num_grover_iters: number of Grover iterations.

        Returns:
            A ``@parametric`` function taking the register specs.
        """
        ae_fn = self.arm_aes[arm_index]
        comp = make_comparison_oracle(ae_fn, threshold, self.ae_precision)
        step = make_search_step(comp, self.arm_index_width)
        return step

    def build_single_arm_ae(self, arm_index: int) -> DSLFunction:
        """Return the coherent AE circuit for a single arm.

        Useful for standalone estimation without Grover search.
        """
        return self.arm_aes[arm_index]

    def register_specs(self) -> list[tuple[str, int]]:
        """Return (name, size) pairs for the search circuit registers."""
        return [
            ("arm_index", self.arm_index_width),
            *self.work_reg_specs,
            ("ae_counting", self.ae_precision),
            ("thresh_reg", self.ae_precision),
            ("cmp_flag", 1),
        ]
