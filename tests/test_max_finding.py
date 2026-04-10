"""Tests for Durr-Hoyer quantum maximum finding."""

from b01t import (
    QReg,
    QiskitBackend,
    coherent,
    h,
)
from b01t.zoo.grover import make_phase_oracle
from b01t.zoo.qae import make_coherent_ae
from b01t.zoo.max_finding import make_comparison_oracle, DurrHoyerRunner
from b01t.zoo.max_finding.durr_hoyer import make_search_step


@coherent
def hadamard_prep(sys: QReg):
    for q in sys:
        h(q)


oracle_11 = make_phase_oracle([1, 1])
oracle_10 = make_phase_oracle([1, 0])


class TestComparisonOracle:
    def test_builds(self):
        """Comparison oracle should build an IR."""
        ae = make_coherent_ae(hadamard_prep, oracle_11)
        comp = make_comparison_oracle(ae, threshold_value=1, precision=2)
        # work(2) + ae_counting(2) + thresh(2) + flag(1)
        ir = comp.build(("work", 2), ("ae_counting", 2), ("thresh", 2), ("flag", 1))
        assert len(ir.ops) > 0

    def test_compiles_to_qiskit(self):
        """Comparison oracle circuit should compile."""
        ae = make_coherent_ae(hadamard_prep, oracle_11)
        comp = make_comparison_oracle(ae, threshold_value=1, precision=2)
        ir = comp.build(("work", 2), ("ae_counting", 2), ("thresh", 2), ("flag", 1))
        qc = QiskitBackend().emit(ir)
        assert qc.num_qubits >= 7
        assert qc.size() > 0

    def test_threshold_zero(self):
        """Threshold 0 should still build (every arm beats it)."""
        ae = make_coherent_ae(hadamard_prep, oracle_11)
        comp = make_comparison_oracle(ae, threshold_value=0, precision=2)
        ir = comp.build(("work", 2), ("ae_counting", 2), ("thresh", 2), ("flag", 1))
        qc = QiskitBackend().emit(ir)
        assert qc.num_qubits >= 7


class TestSearchStep:
    def test_builds(self):
        """Grover search step should build an IR."""
        ae = make_coherent_ae(hadamard_prep, oracle_11)
        comp = make_comparison_oracle(ae, threshold_value=1, precision=2)
        step = make_search_step(comp, arm_index_width=1)
        # arm_idx(1) + work(2) + ae_counting(2) + thresh(2) + flag(1)
        ir = step.build(
            ("arm_idx", 1), ("work", 2),
            ("ae_counting", 2), ("thresh", 2), ("flag", 1),
        )
        assert len(ir.ops) > 0

    def test_compiles_to_qiskit(self):
        """Grover search step should compile to Qiskit."""
        ae = make_coherent_ae(hadamard_prep, oracle_11)
        comp = make_comparison_oracle(ae, threshold_value=1, precision=2)
        step = make_search_step(comp, arm_index_width=1)
        ir = step.build(
            ("arm_idx", 1), ("work", 2),
            ("ae_counting", 2), ("thresh", 2), ("flag", 1),
        )
        qc = QiskitBackend().emit(ir)
        assert qc.num_qubits >= 8


class TestDurrHoyerRunner:
    def test_constructs(self):
        """DurrHoyerRunner should construct with 2 arms."""
        runner = DurrHoyerRunner(
            arm_state_preps=[hadamard_prep, hadamard_prep],
            arm_mark_oracles=[oracle_11, oracle_10],
            ae_precision=2,
            work_reg_specs=[("work", 2)],
        )
        assert runner.num_arms == 2
        assert runner.arm_index_width == 1
        assert len(runner.arm_aes) == 2

    def test_register_specs(self):
        """Register specs should reflect the configuration."""
        runner = DurrHoyerRunner(
            arm_state_preps=[hadamard_prep, hadamard_prep],
            arm_mark_oracles=[oracle_11, oracle_10],
            ae_precision=2,
            work_reg_specs=[("work", 2)],
        )
        specs = runner.register_specs()
        assert ("arm_index", 1) in specs
        assert ("work", 2) in specs
        assert ("ae_counting", 2) in specs
        assert ("cmp_flag", 1) in specs

    def test_build_search_circuit(self):
        """Building a search circuit for one arm should compile."""
        runner = DurrHoyerRunner(
            arm_state_preps=[hadamard_prep, hadamard_prep],
            arm_mark_oracles=[oracle_11, oracle_10],
            ae_precision=2,
            work_reg_specs=[("work", 2)],
        )
        step = runner.build_search_circuit(
            threshold=1, arm_index=0, num_grover_iters=1,
        )
        ir = step.build(*runner.register_specs())
        qc = QiskitBackend().emit(ir)
        assert qc.num_qubits >= 8
        assert qc.size() > 0

    def test_single_arm_ae(self):
        """Single-arm AE should build and compile."""
        runner = DurrHoyerRunner(
            arm_state_preps=[hadamard_prep, hadamard_prep],
            arm_mark_oracles=[oracle_11, oracle_10],
            ae_precision=2,
            work_reg_specs=[("work", 2)],
        )
        ae = runner.build_single_arm_ae(0)
        ir = ae.build(("counting", 2), ("work", 2))
        qc = QiskitBackend().emit(ir)
        assert qc.num_qubits >= 4
