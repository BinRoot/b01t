"""Tests for Simon's oracle and algorithm."""
from b01t import (
    QiskitBackend,
    Certification,
    lower_exact_program,
    exact_program_to_json,
    exact_program_from_json,
)
from demos.simon import make_simon_oracle, make_simon_algorithm


class TestOracleConstruction:
    def test_2_qubit(self):
        oracle = make_simon_oracle([1, 1])
        prog = oracle.build_exact(("inp", 2), ("out", 2))
        assert prog.certification == Certification.SAFE

    def test_3_qubit(self):
        oracle = make_simon_oracle([1, 0, 1])
        prog = oracle.build_exact(("inp", 3), ("out", 3))
        assert prog.certification == Certification.SAFE

    def test_single_bit_secret(self):
        oracle = make_simon_oracle([0, 1, 0])
        prog = oracle.build_exact(("inp", 3), ("out", 3))
        assert prog.certification == Certification.SAFE

    def test_all_ones(self):
        oracle = make_simon_oracle([1, 1, 1])
        prog = oracle.build_exact(("inp", 3), ("out", 3))
        assert prog.certification == Certification.SAFE


class TestOracleValidation:
    def test_invalid_entry(self):
        try:
            make_simon_oracle([0, 3])
            assert False, "expected ValueError"
        except ValueError:
            pass

    def test_empty(self):
        try:
            make_simon_oracle([])
            assert False, "expected ValueError"
        except ValueError:
            pass


class TestSerialization:
    def test_round_trip(self):
        oracle = make_simon_oracle([1, 0, 1])
        prog = oracle.build_exact(("inp", 3), ("out", 3))
        json_str = exact_program_to_json(prog)
        restored = exact_program_from_json(json_str)
        assert restored.name == prog.name
        assert len(restored.ops) == len(prog.ops)


class TestQiskitCompilation:
    def test_oracle_compiles(self):
        oracle = make_simon_oracle([1, 1, 0])
        prog = oracle.build_exact(("inp", 3), ("out", 3))
        ir = lower_exact_program(prog)
        qc = QiskitBackend().emit(ir)
        assert qc.num_qubits == 6

    def test_algorithm_compiles(self):
        algo = make_simon_algorithm([1, 0, 1])
        ir = algo.build(("inp", 3), ("out", 3))
        qc = QiskitBackend().emit(ir)
        assert qc.num_qubits == 6
        assert qc.size() > 0


class TestAlgorithm:
    def test_builds_as_adaptive(self):
        algo = make_simon_algorithm([1, 1])
        ir = algo.build(("inp", 2), ("out", 2))
        assert not ir.is_safe
        assert len(ir.ops) > 0
