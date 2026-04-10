"""Tests for QAE circuit and classical estimation."""
from b01t import (
    QReg,
    QiskitBackend,
    coherent,
    h,
    lower_exact_program,
)
from b01t.zoo.grover import make_phase_oracle
from b01t.zoo.qae import (
    zero_state_reflection,
    make_qae_round,
    make_qae_schedule,
    simulate_qae,
    ml_estimate,
    clopper_pearson,
)


@coherent
def hadamard_prep(sys: QReg):
    for q in sys:
        h(q)


oracle_11 = make_phase_oracle([1, 1])


class TestQAERound:
    def test_depth_0_builds(self):
        """Depth 0 = just state prep + measure."""
        circuit = make_qae_round(hadamard_prep, oracle_11, depth=0)
        ir = circuit.build(("sys", 2))
        assert not ir.is_safe  # adaptive
        assert len(ir.ops) > 0

    def test_depth_1_builds(self):
        circuit = make_qae_round(hadamard_prep, oracle_11, depth=1)
        ir = circuit.build(("sys", 2))
        assert len(ir.ops) > 0

    def test_depth_4_compiles(self):
        circuit = make_qae_round(hadamard_prep, oracle_11, depth=4)
        ir = circuit.build(("sys", 2))
        qc = QiskitBackend().emit(ir)
        assert qc.num_qubits > 0


class TestQAESchedule:
    def test_creates_correct_number_of_circuits(self):
        circuits = make_qae_schedule(hadamard_prep, oracle_11, max_depth=4)
        assert len(circuits) == 4

    def test_all_circuits_compile(self):
        circuits = make_qae_schedule(hadamard_prep, oracle_11, max_depth=3)
        for circuit in circuits:
            ir = circuit.build(("sys", 2))
            qc = QiskitBackend().emit(ir)
            assert qc.num_qubits > 0


class TestClassicalEstimation:
    def test_simulate_qae(self):
        results = simulate_qae(0.25, max_depth=4, shots_per_depth=100)
        assert len(results) == 5  # depths 0..4
        for depth, successes, total in results:
            assert 0 <= successes <= total

    def test_ml_estimate_recovers_theta(self):
        """MLE should approximately recover the true probability."""
        import math
        true_p = 0.25
        results = simulate_qae(true_p, max_depth=6, shots_per_depth=500, seed=123)
        theta = ml_estimate(results)
        estimated_p = math.sin(theta) ** 2
        assert abs(estimated_p - true_p) < 0.1

    def test_clopper_pearson(self):
        lo, hi = clopper_pearson(25, 100)
        assert lo < 0.25 < hi
        assert 0 <= lo and hi <= 1
