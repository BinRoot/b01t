"""Tests for ripple-carry adder and comparator."""
from b01t import (
    QReg,
    QiskitBackend,
    Certification,
    coherent,
    ancilla,
    compute,
    apply,
    uncompute,
    cx,
    lower_exact_program,
)
from b01t.kit.arithmetic import (
    ripple_carry_add_wires,
    controlled_add_wires,
    less_than,
)
from b01t.kit.arithmetic.adder import _maj_wires, _uma_wires


# ---------------------------------------------------------------------------
# Adder tests
# ---------------------------------------------------------------------------

class TestMajUma:
    """MAJ and UMA are inverse of each other (up to sum extraction)."""

    def test_maj_is_coherent(self):
        @coherent
        def test_maj(r: QReg):
            _maj_wires(r[0], r[1], r[2])

        prog = test_maj.build_exact(("r", 3))
        assert prog.certification == Certification.SAFE

    def test_uma_is_coherent(self):
        @coherent
        def test_uma(r: QReg):
            _uma_wires(r[0], r[1], r[2])

        prog = test_uma.build_exact(("r", 3))
        assert prog.certification == Certification.SAFE


class TestRippleCarryAdd:
    """Wire-level Cuccaro adder builds and compiles."""

    def _make_adder(self, n):
        """Build a @coherent adder with ancilla for the carry wire."""
        @coherent
        def adder(a: QReg, b: QReg, cin: QReg):
            ripple_carry_add_wires(a.wires(), b.wires(), cin[0])
        return adder

    def test_2bit_is_safe(self):
        adder = self._make_adder(2)
        prog = adder.build_exact(("a", 2), ("b", 2), ("cin", 1))
        assert prog.certification == Certification.SAFE

    def test_4bit_is_safe(self):
        adder = self._make_adder(4)
        prog = adder.build_exact(("a", 4), ("b", 4), ("cin", 1))
        assert prog.certification == Certification.SAFE

    def test_2bit_compiles_to_qiskit(self):
        adder = self._make_adder(2)
        prog = adder.build_exact(("a", 2), ("b", 2), ("cin", 1))
        ir = lower_exact_program(prog)
        qc = QiskitBackend().emit(ir)
        assert qc.num_qubits == 5  # 2+2+1

    def test_gate_count_scales_linearly(self):
        """Cuccaro adder uses O(n) gates."""
        for n in [2, 4, 8]:
            adder = self._make_adder(n)
            prog = adder.build_exact(("a", n), ("b", n), ("cin", 1))
            # MAJ = 3 gates, UMA = 3 gates, n iterations each = 6n gates
            assert len(prog.ops) == 6 * n


class TestControlledAdd:
    """Controlled adder builds and compiles."""

    def test_2bit_is_safe(self):
        @coherent
        def ctrl_adder(ctrl: QReg, a: QReg, b: QReg, cin: QReg):
            controlled_add_wires(ctrl[0], a.wires(), b.wires(), cin[0])

        prog = ctrl_adder.build_exact(
            ("ctrl", 1), ("a", 2), ("b", 2), ("cin", 1))
        assert prog.certification == Certification.SAFE

    def test_compiles_to_qiskit(self):
        @coherent
        def ctrl_adder(ctrl: QReg, a: QReg, b: QReg, cin: QReg):
            controlled_add_wires(ctrl[0], a.wires(), b.wires(), cin[0])

        prog = ctrl_adder.build_exact(
            ("ctrl", 1), ("a", 2), ("b", 2), ("cin", 1))
        ir = lower_exact_program(prog)
        qc = QiskitBackend().emit(ir)
        assert qc.num_qubits == 6  # 1+2+2+1


# ---------------------------------------------------------------------------
# Comparator tests
# ---------------------------------------------------------------------------

class TestLessThan:
    """@coherent less_than using compute/apply/uncompute."""

    def test_2bit_is_safe(self):
        prog = less_than.build_exact(("a", 2), ("b", 2), ("result", 1))
        assert prog.certification == Certification.SAFE

    def test_3bit_is_safe(self):
        prog = less_than.build_exact(("a", 3), ("b", 3), ("result", 1))
        assert prog.certification == Certification.SAFE

    def test_4bit_is_safe(self):
        prog = less_than.build_exact(("a", 4), ("b", 4), ("result", 1))
        assert prog.certification == Certification.SAFE

    def test_compiles_to_qiskit(self):
        prog = less_than.build_exact(("a", 3), ("b", 3), ("result", 1))
        ir = lower_exact_program(prog)
        qc = QiskitBackend().emit(ir)
        assert qc.num_qubits > 0

    def test_1bit_is_safe(self):
        """Edge case: single-bit comparison."""
        prog = less_than.build_exact(("a", 1), ("b", 1), ("result", 1))
        assert prog.certification == Certification.SAFE

    def test_uses_ancilla(self):
        prog = less_than.build_exact(("a", 3), ("b", 3), ("result", 1))
        anc_regs = [r for r in prog.regs if r.kind == "anc"]
        assert len(anc_regs) > 0
