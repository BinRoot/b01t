"""Tests for Shor's algorithm circuit and classical post-processing."""
from b01t import QiskitBackend
from demos.shor import make_shor_circuit
from demos.shor.classical import (
    find_period_classical,
    extract_period,
    factor_from_period,
    continued_fraction_convergents,
)


class TestClassical:
    """Classical post-processing functions."""

    def test_find_period_2_mod_7(self):
        assert find_period_classical(2, 7) == 3  # 2^3 = 8 = 1 mod 7

    def test_find_period_3_mod_7(self):
        assert find_period_classical(3, 7) == 6  # 3^6 = 729 = 1 mod 7

    def test_find_period_2_mod_15(self):
        assert find_period_classical(2, 15) == 4

    def test_find_period_7_mod_15(self):
        assert find_period_classical(7, 15) == 4

    def test_continued_fractions(self):
        convergents = list(continued_fraction_convergents(3, 8))
        # 3/8 = 0 + 1/(2 + 1/(1 + 1/2))
        # Convergents: 0/1, 1/3, ...
        assert len(convergents) > 0
        # Last convergent should be 3/8
        p, q = convergents[-1]
        assert p * 8 == q * 3 or abs(p / q - 3 / 8) < 0.01

    def test_extract_period(self):
        # If measurement = s/r * 2^t, with r=4, s=1, t=6:
        # measurement = 1/4 * 64 = 16
        r = extract_period(16, 6, 15)
        assert r == 4

    def test_factor_from_period(self):
        # 7^4 = 2401, 7^2 = 49. gcd(49-1, 15)=gcd(48,15)=3.
        result = factor_from_period(7, 4, 15)
        assert result is not None
        f1, f2 = result
        assert f1 * f2 == 15
        assert f1 > 1 and f2 > 1


class TestShorCircuit:
    """The full Shor circuit builds and compiles."""

    def test_builds(self):
        """Factor 15 with a=7, 6 counting bits."""
        shor = make_shor_circuit(a_val=7, N=15, num_counting_bits=6)
        n = 15 .bit_length()  # 4
        ir = shor.build(
            ("counting", 6), ("y", n), ("acc", n), ("scratch", n + 3))
        assert not ir.is_safe  # adaptive (measures)
        assert len(ir.ops) > 0

    def test_compiles_to_qiskit(self):
        """Compile the full Shor circuit to Qiskit."""
        shor = make_shor_circuit(a_val=2, N=7, num_counting_bits=6)
        n = 7 .bit_length()  # 3
        ir = shor.build(
            ("counting", 6), ("y", n), ("acc", n), ("scratch", n + 3))
        qc = QiskitBackend().emit(ir)
        # counting(6) + y(3) + acc(3) + scratch(6) = 18 qubits
        assert qc.num_qubits == 18
        assert qc.size() > 0

    def test_small_instance(self):
        """Smallest non-trivial: factor 15, a=2, 8 counting bits."""
        shor = make_shor_circuit(a_val=2, N=15, num_counting_bits=8)
        n = 15 .bit_length()  # 4
        ir = shor.build(
            ("counting", 8), ("y", n), ("acc", n), ("scratch", n + 3))
        qc = QiskitBackend().emit(ir)
        # counting(8) + y(4) + acc(4) + scratch(7) = 23 qubits
        assert qc.num_qubits == 23
