"""Tests for QFT, QPE, and Shor's algorithm."""
from b01t import (
    QReg,
    QiskitBackend,
    parametric,
    h,
    lower_exact_program,
)
from b01t.zoo.qft import qft, inverse_qft
from b01t.zoo.qpe import make_qpe


class TestQFT:
    def test_builds(self):
        ir = qft.build(("reg", 3))
        assert len(ir.ops) > 0

    def test_compiles_to_qiskit(self):
        ir = qft.build(("reg", 4))
        qc = QiskitBackend().emit(ir)
        assert qc.num_qubits == 4

    def test_inverse_builds(self):
        ir = inverse_qft.build(("reg", 3))
        assert len(ir.ops) > 0

    def test_inverse_compiles(self):
        ir = inverse_qft.build(("reg", 4))
        qc = QiskitBackend().emit(ir)
        assert qc.num_qubits == 4

    def test_gate_count_scales(self):
        """QFT on n qubits uses O(n^2) gates."""
        ir3 = qft.build(("reg", 3))
        ir4 = qft.build(("reg", 4))
        assert len(ir4.ops) > len(ir3.ops)


class TestQPE:
    def test_builds_with_identity_oracle(self):
        """QPE with a trivial oracle (does nothing) should still build."""
        @parametric
        def trivial_oracle(ctrl: QReg, work: QReg):
            pass  # identity; eigenvalue is 1, so phase is 0

        qpe_fn = make_qpe(trivial_oracle)
        ir = qpe_fn.build(("counting", 3), ("work", 2))
        assert len(ir.ops) > 0

    def test_compiles_to_qiskit(self):
        @parametric
        def trivial_oracle(ctrl: QReg, work: QReg):
            pass

        qpe_fn = make_qpe(trivial_oracle)
        ir = qpe_fn.build(("counting", 3), ("work", 2))
        qc = QiskitBackend().emit(ir)
        assert qc.num_qubits == 5
