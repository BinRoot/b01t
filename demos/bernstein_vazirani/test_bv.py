"""Tests for Bernstein-Vazirani oracle and algorithm."""
from b01t import (
    QiskitBackend,
    Certification,
    lower_exact_program,
    exact_program_to_json,
    exact_program_from_json,
)
from demos.bernstein_vazirani import make_bv_oracle, make_bv_algorithm


class TestOracleConstruction:
    def test_single_bit(self):
        oracle = make_bv_oracle([1])
        prog = oracle.build_exact(("inp", 1), ("tgt", 1))
        assert prog.certification == Certification.SAFE

    def test_multi_bit(self):
        oracle = make_bv_oracle([1, 0, 1, 1])
        prog = oracle.build_exact(("inp", 4), ("tgt", 1))
        assert prog.certification == Certification.SAFE

    def test_zero_string(self):
        oracle = make_bv_oracle([0, 0, 0])
        prog = oracle.build_exact(("inp", 3), ("tgt", 1))
        assert prog.certification == Certification.SAFE
        assert len(prog.ops) == 0

    def test_gate_count_matches_hamming_weight(self):
        oracle = make_bv_oracle([1, 0, 1, 0, 1])
        prog = oracle.build_exact(("inp", 5), ("tgt", 1))
        assert len(prog.ops) == 3  # three CX gates


class TestOracleValidation:
    def test_invalid_entry(self):
        try:
            make_bv_oracle([0, 2])
            assert False, "expected ValueError"
        except ValueError:
            pass

    def test_empty(self):
        try:
            make_bv_oracle([])
            assert False, "expected ValueError"
        except ValueError:
            pass


class TestSerialization:
    def test_round_trip(self):
        oracle = make_bv_oracle([1, 1, 0])
        prog = oracle.build_exact(("inp", 3), ("tgt", 1))
        json_str = exact_program_to_json(prog)
        restored = exact_program_from_json(json_str)
        assert restored.name == prog.name
        assert len(restored.ops) == len(prog.ops)


class TestQiskitCompilation:
    def test_oracle_compiles(self):
        oracle = make_bv_oracle([1, 0, 1])
        prog = oracle.build_exact(("inp", 3), ("tgt", 1))
        ir = lower_exact_program(prog)
        qc = QiskitBackend().emit(ir)
        assert qc.num_qubits == 4

    def test_algorithm_compiles(self):
        algo = make_bv_algorithm([1, 0, 1])
        ir = algo.build(("inp", 3), ("tgt", 1))
        qc = QiskitBackend().emit(ir)
        assert qc.num_qubits == 4
        assert qc.size() > 0


class TestAlgorithm:
    def test_builds_as_adaptive(self):
        algo = make_bv_algorithm([1, 1, 0])
        ir = algo.build(("inp", 3), ("tgt", 1))
        assert not ir.is_safe
        assert len(ir.ops) > 0
