"""Regression test: ancilla coalescing must not merge ancillae across par branches.

If left and right branches of a par() each allocate ancilla, those ancillae
must stay on separate physical wires after lowering. Merging them would let
both branches write to the same qubits simultaneously, violating par semantics.
"""
from qiskit.quantum_info import Statevector

from b01t import (
    QReg, QiskitBackend, Certification,
    coherent, x, z, cx, ccx, h,
    lower_exact_program, par,
)
from b01t.kit import ancilla, compute, phase, uncompute


@coherent
def par_with_ancilla(sys: QReg):
    """Two parallel branches, each using its own ancilla.

    Left:  phase-flip if sys[0]=1 (via ancilla)
    Right: phase-flip if sys[1]=1 (via ancilla)

    Correct result: phase flip on |11>, |10>, |01> but not |00>.
    (Each branch independently flips its qubit's phase.)
    """
    def left():
        with ancilla(1) as anc:
            compute(lambda: cx(sys[0], anc[0]))
            phase(lambda: z(anc[0]))
            uncompute()

    def right():
        with ancilla(1) as anc:
            compute(lambda: cx(sys[1], anc[0]))
            phase(lambda: z(anc[0]))
            uncompute()

    par(left, right)


class TestParAncillaDisjoint:
    """Ancilla registers in parallel branches must not be coalesced."""

    def test_lowered_ancillae_are_distinct(self):
        """After lowering, the two ancilla blocks inside par must reference
        different physical wires."""
        prog = par_with_ancilla.build_exact(("sys", 2))
        ir = lower_exact_program(prog)

        # Find the ParOp
        par_op = None
        for op in ir.ops:
            from b01t.core.types import ParOp
            if isinstance(op, ParOp):
                par_op = op
                break
        assert par_op is not None

        # Collect ancilla wire names used in left vs right
        def _collect_wires(ops):
            wires = set()
            for op in ops:
                from b01t.core.types import AncillaBlockOp, GateOp
                if isinstance(op, AncillaBlockOp):
                    for g in op.compute_ops + op.phase_ops + op.uncompute_ops:
                        wires.update(g.wires)
                elif isinstance(op, GateOp):
                    wires.update(op.wires)
            return wires

        left_wires = _collect_wires(par_op.left_ops)
        right_wires = _collect_wires(par_op.right_ops)

        # System wires are allowed to differ (left uses sys[0], right uses sys[1]).
        # But ancilla wires must NOT overlap.
        left_anc = {w for w in left_wires if w.kind == "anc"}
        right_anc = {w for w in right_wires if w.kind == "anc"}

        assert left_anc.isdisjoint(right_anc), (
            f"Ancilla wires overlap across par branches! "
            f"left={left_anc}, right={right_anc}")

    def test_simulation_correctness(self):
        """Simulate the par circuit and verify correct phase kickback.

        Apply to |+>|+> = H|0>H|0>. Each branch independently flips
        phase of its qubit. The combined effect is Z⊗Z.

        H|0> = |+>. Z|+> = |->. So the output should be |->|-> = HZ|0> ⊗ HZ|0>.

        Measure in X basis (apply H then measure): should get |11> deterministically.
        """
        # Build: H on both, then par_with_ancilla, then H on both
        @coherent
        def test_circuit(sys: QReg):
            h(sys[0])
            h(sys[1])
            par_with_ancilla(sys)
            h(sys[0])
            h(sys[1])

        prog = test_circuit.build_exact(("sys", 2))
        ir = lower_exact_program(prog)
        qc = QiskitBackend().emit(ir)

        sv = Statevector.from_instruction(qc)
        probs = sv.probabilities_dict()
        outcomes = {k: v for k, v in probs.items() if v > 0.99}

        # With correct lowering: H Z H = X, so both qubits flip → |11>
        # The ancilla qubits should all be |0>
        assert len(outcomes) == 1, f"Expected deterministic outcome, got {probs}"
        result = list(outcomes.keys())[0]
        # sys qubits are the first 2 (qubits 0 and 1)
        sys_bits = result[-2:]  # last 2 chars = qubits 0,1
        assert sys_bits == "11", (
            f"Expected sys=|11> (Z⊗Z phase kickback), got |{sys_bits}>. "
            f"Full state: {result}")
