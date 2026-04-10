"""Coherent amplitude estimation (Brassard et al., 2002).

QPE on the Grover iterate G = A S_0 A† O_chi.  The counting register
receives an estimate of theta where sin^2(theta) = Pr[good].

Unlike IQAE (qae_circuit.py), this is a single coherent unitary --
no intermediate measurements, no classical adaptation.  It can
therefore run inside Durr-Hoyer's Grover loop.

Supports multi-register oracles: the state_prep and mark_oracle may
take any number of QRegs (e.g. the rollout oracle takes ~10 registers).

@parametric because QPE uses inverse QFT (continuous rotations).
"""

from typing import Callable, Union

from b01t.core import QReg, coherent, parametric
from b01t.core.exact_builder import ExactDSLFunction
from b01t.core.gates import x, z, cz, h, mcx
from b01t.kit import ancilla, compute, phase, uncompute, adjoint
from b01t.kit.controlled import controlled_call, inline_exact
from b01t.zoo.qpe import make_qpe


def _make_multi_reg_grover_iterate(state_prep, mark_oracle):
    """Build a Grover iterate G for multi-register state_prep/oracle.

    G = mark_oracle . adjoint(state_prep) . S_0 . state_prep

    The zero-state reflection S_0 acts on all qubits across all
    work registers simultaneously.
    """

    @coherent
    def grover_iterate(*regs: QReg):
        # O_chi: mark good states
        mark_oracle(*regs)
        # A†: undo state prep
        adjoint(state_prep, *regs)
        # S_0: reflect about |0...0> across all qubits
        all_wires = []
        for r in regs:
            all_wires.extend(r.wires())
        n = len(all_wires)
        for w in all_wires:
            x(w)
        if n == 1:
            z(all_wires[0])
        elif n == 2:
            cz(all_wires[0], all_wires[1])
        else:
            with ancilla(1) as anc:
                compute(lambda: mcx(all_wires[:-1], anc[0]))
                phase(lambda: cz(anc[0], all_wires[-1]))
                uncompute()
        for w in all_wires:
            x(w)
        # A: re-apply state prep
        state_prep(*regs)

    return grover_iterate


def make_coherent_ae(
    state_prep: Union[ExactDSLFunction, Callable],
    mark_oracle: Union[ExactDSLFunction, Callable],
):
    """Build a coherent (QPE-based) amplitude estimation circuit.

    Args:
        state_prep: ``@coherent`` state preparation A.
                    May take one or more ``QReg`` arguments.
        mark_oracle: ``@coherent`` phase oracle O_chi.
                     Must flip the phase of "good" states.
                     Same signature as *state_prep*.

    Returns:
        A ``@parametric`` function ``(counting: QReg, *work_regs: QReg)``
        that:

        1. Applies *state_prep* on the work registers to prepare A|0>.
        2. Runs QPE on the Grover iterate
           G = mark_oracle . adjoint(state_prep) . S_0 . state_prep,
           writing the theta estimate into *counting*.

        After execution, measuring *counting* yields an approximation
        of theta such that sin^2(theta) = Pr[good].  The precision is
        determined by ``len(counting)``.
    """
    # Build the multi-register Grover iterate G (a @coherent ExactDSLFunction).
    grover_iterate = _make_multi_reg_grover_iterate(state_prep, mark_oracle)

    # QPE oracle: apply controlled-G^(2^k) for each counting bit k.
    def _qpe_oracle(counting: QReg, *work_regs: QReg):
        for k in range(len(counting)):
            for _ in range(1 << k):
                controlled_call(counting[k], grover_iterate, *work_regs)

    # Compose with the existing QPE module.
    qpe_fn = make_qpe(_qpe_oracle)

    @parametric
    def coherent_ae(counting: QReg, *work_regs: QReg):
        # Step 1: prepare A|0> on the work registers.
        # Use inline_exact because state_prep is @coherent and may
        # call other @coherent sub-functions that need an exact context.
        inline_exact(state_prep, *work_regs)
        # Step 2: QPE estimates the eigenvalue of G.
        qpe_fn(counting, *work_regs)

    return coherent_ae
