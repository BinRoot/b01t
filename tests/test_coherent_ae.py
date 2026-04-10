"""Tests for coherent (QPE-based) amplitude estimation."""

from b01t import (
    QReg,
    QiskitBackend,
    coherent,
    h,
    lower_exact_program,
)
from b01t.zoo.grover import make_phase_oracle
from b01t.zoo.qae import make_coherent_ae


@coherent
def hadamard_prep(sys: QReg):
    for q in sys:
        h(q)


oracle_11 = make_phase_oracle([1, 1])


class TestCoherentAE:
    def test_builds(self):
        """Coherent AE should build an IR without errors."""
        ae = make_coherent_ae(hadamard_prep, oracle_11)
        ir = ae.build(("counting", 2), ("work", 2))
        assert len(ir.ops) > 0

    def test_compiles_to_qiskit(self):
        """Coherent AE circuit should compile to Qiskit."""
        ae = make_coherent_ae(hadamard_prep, oracle_11)
        ir = ae.build(("counting", 2), ("work", 2))
        qc = QiskitBackend().emit(ir)
        # counting(2) + work(2) + ancilla from oracle
        assert qc.num_qubits >= 4
        assert qc.size() > 0

    def test_precision_3(self):
        """Higher precision (3 bits) should also compile."""
        ae = make_coherent_ae(hadamard_prep, oracle_11)
        ir = ae.build(("counting", 3), ("work", 2))
        qc = QiskitBackend().emit(ir)
        assert qc.num_qubits >= 5

    def test_3qubit_oracle(self):
        """Coherent AE with a 3-qubit system and different oracle."""
        oracle_101 = make_phase_oracle([1, 0, 1])
        ae = make_coherent_ae(hadamard_prep, oracle_101)
        ir = ae.build(("counting", 2), ("work", 3))
        qc = QiskitBackend().emit(ir)
        assert qc.num_qubits >= 5
        assert qc.size() > 0

    def test_higher_precision_has_more_gates(self):
        """More precision bits should produce more gates (more controlled-G calls)."""
        ae = make_coherent_ae(hadamard_prep, oracle_11)
        ir2 = ae.build(("counting", 2), ("work", 2))
        ir3 = ae.build(("counting", 3), ("work", 2))
        qc2 = QiskitBackend().emit(ir2)
        qc3 = QiskitBackend().emit(ir3)
        assert qc3.size() > qc2.size()
