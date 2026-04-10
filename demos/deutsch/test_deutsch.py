"""Tests for Deutsch's algorithm oracle and full algorithm."""
from b01t import (
    QReg,
    QiskitBackend,
    Certification,
    lower_exact_program,
    exact_program_to_json,
    exact_program_from_json,
)
from demos.deutsch import make_deutsch_oracle, make_deutsch_algorithm


class TestOracleConstruction:
    """All four oracles build as @coherent and are safe."""

    def test_constant_zero(self):
        oracle = make_deutsch_oracle(0, 0)
        prog = oracle.build_exact(("inp", 1), ("tgt", 1))
        assert prog.certification == Certification.SAFE

    def test_constant_one(self):
        oracle = make_deutsch_oracle(1, 1)
        prog = oracle.build_exact(("inp", 1), ("tgt", 1))
        assert prog.certification == Certification.SAFE

    def test_balanced_identity(self):
        oracle = make_deutsch_oracle(0, 1)
        prog = oracle.build_exact(("inp", 1), ("tgt", 1))
        assert prog.certification == Certification.SAFE

    def test_balanced_negation(self):
        oracle = make_deutsch_oracle(1, 0)
        prog = oracle.build_exact(("inp", 1), ("tgt", 1))
        assert prog.certification == Certification.SAFE


class TestOracleGateCounts:
    """Verify the expected gate structure for each oracle."""

    def test_constant_zero_has_no_ops(self):
        oracle = make_deutsch_oracle(0, 0)
        prog = oracle.build_exact(("inp", 1), ("tgt", 1))
        assert len(prog.ops) == 0

    def test_constant_one_has_one_x(self):
        oracle = make_deutsch_oracle(1, 1)
        prog = oracle.build_exact(("inp", 1), ("tgt", 1))
        assert len(prog.ops) == 1

    def test_balanced_identity_has_one_cx(self):
        oracle = make_deutsch_oracle(0, 1)
        prog = oracle.build_exact(("inp", 1), ("tgt", 1))
        assert len(prog.ops) == 1

    def test_balanced_negation_has_two_ops(self):
        oracle = make_deutsch_oracle(1, 0)
        prog = oracle.build_exact(("inp", 1), ("tgt", 1))
        assert len(prog.ops) == 2


class TestOracleValidation:
    def test_invalid_f0(self):
        try:
            make_deutsch_oracle(2, 0)
            assert False, "expected ValueError"
        except ValueError:
            pass

    def test_invalid_f1(self):
        try:
            make_deutsch_oracle(0, -1)
            assert False, "expected ValueError"
        except ValueError:
            pass


class TestSerialization:
    def test_round_trip(self):
        oracle = make_deutsch_oracle(1, 0)
        prog = oracle.build_exact(("inp", 1), ("tgt", 1))
        json_str = exact_program_to_json(prog)
        restored = exact_program_from_json(json_str)
        assert restored.name == prog.name
        assert len(restored.ops) == len(prog.ops)


class TestQiskitCompilation:
    def test_all_oracles_compile(self):
        for f0, f1 in [(0, 0), (0, 1), (1, 0), (1, 1)]:
            oracle = make_deutsch_oracle(f0, f1)
            prog = oracle.build_exact(("inp", 1), ("tgt", 1))
            ir = lower_exact_program(prog)
            qc = QiskitBackend().emit(ir)
            assert qc.num_qubits == 2

    def test_algorithm_compiles(self):
        algo = make_deutsch_algorithm(0, 1)
        ir = algo.build(("inp", 1), ("tgt", 1))
        qc = QiskitBackend().emit(ir)
        assert qc.num_qubits == 2
        assert qc.size() > 0


class TestAlgorithm:
    def test_builds_as_adaptive(self):
        algo = make_deutsch_algorithm(1, 0)
        ir = algo.build(("inp", 1), ("tgt", 1))
        assert not ir.is_safe  # adaptive (has measurement)
        assert len(ir.ops) > 0

    def test_all_four_variants_build(self):
        for f0, f1 in [(0, 0), (0, 1), (1, 0), (1, 1)]:
            algo = make_deutsch_algorithm(f0, f1)
            ir = algo.build(("inp", 1), ("tgt", 1))
            assert len(ir.ops) > 0
