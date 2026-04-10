"""Small-instance correctness tests: simulate circuits and verify outputs.

Uses Qiskit's Statevector simulator to check that circuits produce
the classically expected basis state outputs.
"""
from qiskit.quantum_info import Statevector

from b01t import (
    QReg, QiskitBackend, coherent, primitive, x, cx, ccx, h, z,
    lower_exact_program,
)
from b01t.kit import ancilla, compute, phase, apply, uncompute
from b01t.kit.arithmetic import (
    controlled_inc_wires,
    ripple_carry_add_wires,
    int_to_bits,
    apply_pattern_x_wires,
)
from b01t.kit.arithmetic.comparator import less_than


def _simulate(coherent_fn, reg_specs, input_bits=None):
    """Build a @coherent function, optionally prepend X gates for input,
    simulate, and return the output bitstring (dict of probabilities).

    input_bits: dict of {qubit_index: 1} for qubits that should be |1>.
    """
    prog = coherent_fn.build_exact(*reg_specs)
    ir = lower_exact_program(prog)
    qc = QiskitBackend().emit(ir)

    if input_bits:
        from qiskit import QuantumCircuit
        prep = QuantumCircuit(qc.num_qubits)
        for idx in input_bits:
            prep.x(idx)
        qc = prep.compose(qc)

    sv = Statevector.from_instruction(qc)
    probs = sv.probabilities_dict()
    # Return the single deterministic outcome
    outcomes = {k: v for k, v in probs.items() if v > 0.99}
    assert len(outcomes) == 1, f"Expected deterministic output, got {probs}"
    return list(outcomes.keys())[0]


def _bits_to_int(bits_str, start, width):
    """Extract integer from a bitstring (Qiskit: MSB-first, qubit 0 at right)."""
    # Qiskit bitstrings: bit 0 is rightmost
    val = 0
    for i in range(width):
        if bits_str[-(start + i + 1)] == '1':
            val |= (1 << i)
    return val


# -----------------------------------------------------------------------
# controlled_inc_wires
# -----------------------------------------------------------------------

class TestControlledIncCorrectness:
    """Verify controlled increment produces the right integer values."""

    def _make_inc(self):
        @coherent
        def inc(ctrl: QReg, reg: QReg):
            controlled_inc_wires(ctrl[0], reg.wires())
        return inc

    def test_inc_zero_gives_one(self):
        """ctrl=1, reg=000 → reg=001 (0+1=1)."""
        inc = self._make_inc()
        # qubit layout: ctrl(1) + reg(3) = 4 qubits
        # ctrl = qubit 0, reg = qubits 1,2,3
        result = _simulate(inc, (("ctrl", 1), ("reg", 3)), input_bits={0: 1})
        # ctrl stays 1, reg becomes 1 (binary 001 in LSB-first = qubit1=1)
        ctrl_val = int(result[-1])  # qubit 0
        reg_val = _bits_to_int(result, 1, 3)
        assert ctrl_val == 1
        assert reg_val == 1

    def test_inc_three_gives_four(self):
        """ctrl=1, reg=011 (3) → reg=100 (4)."""
        inc = self._make_inc()
        # reg=3: bits [1,1,0] LSB-first → qubits 1,2 set
        result = _simulate(inc, (("ctrl", 1), ("reg", 3)),
                          input_bits={0: 1, 1: 1, 2: 1})
        ctrl_val = int(result[-1])
        reg_val = _bits_to_int(result, 1, 3)
        assert ctrl_val == 1
        assert reg_val == 4

    def test_inc_seven_wraps_to_zero(self):
        """ctrl=1, reg=111 (7) → reg=000 (0 mod 8)."""
        inc = self._make_inc()
        result = _simulate(inc, (("ctrl", 1), ("reg", 3)),
                          input_bits={0: 1, 1: 1, 2: 1, 3: 1})
        reg_val = _bits_to_int(result, 1, 3)
        assert reg_val == 0

    def test_ctrl_zero_no_change(self):
        """ctrl=0, reg=011 (3) → reg=011 (3)."""
        inc = self._make_inc()
        result = _simulate(inc, (("ctrl", 1), ("reg", 3)),
                          input_bits={1: 1, 2: 1})  # ctrl=0, reg=3
        reg_val = _bits_to_int(result, 1, 3)
        assert reg_val == 3


# -----------------------------------------------------------------------
# ripple_carry_add_wires
# -----------------------------------------------------------------------

class TestAdderCorrectness:
    """Verify Cuccaro adder produces correct sums."""

    def _make_adder(self, n):
        @coherent
        def adder(a: QReg, b: QReg, cin: QReg):
            ripple_carry_add_wires(a.wires(), b.wires(), cin[0])
        return adder

    def _run_add(self, n, a_val, b_val):
        adder = self._make_adder(n)
        # Layout: a(n) + b(n) + cin(1)
        input_bits = {}
        a_bits = int_to_bits(a_val, n)
        b_bits = int_to_bits(b_val, n)
        for i in range(n):
            if a_bits[i]:
                input_bits[i] = 1
            if b_bits[i]:
                input_bits[n + i] = 1
        result = _simulate(adder, (("a", n), ("b", n), ("cin", 1)), input_bits)
        a_out = _bits_to_int(result, 0, n)
        b_out = _bits_to_int(result, n, n)
        cin_out = int(result[-(2 * n + 1)])
        return a_out, b_out, cin_out

    def test_1_plus_2(self):
        a_out, b_out, cin = self._run_add(3, 1, 2)
        assert a_out == 1  # preserved
        assert b_out == 3  # 1 + 2 = 3
        assert cin == 0    # carry restored

    def test_3_plus_5(self):
        a_out, b_out, cin = self._run_add(4, 3, 5)
        assert a_out == 3
        assert b_out == 8  # 3 + 5 = 8
        assert cin == 0

    def test_7_plus_7_mod8(self):
        a_out, b_out, cin = self._run_add(3, 7, 7)
        assert a_out == 7
        assert b_out == 6  # 7 + 7 = 14, mod 8 = 6
        assert cin == 0

    def test_0_plus_0(self):
        a_out, b_out, cin = self._run_add(3, 0, 0)
        assert a_out == 0
        assert b_out == 0
        assert cin == 0


# -----------------------------------------------------------------------
# less_than comparator
# -----------------------------------------------------------------------

class TestComparatorCorrectness:
    """Verify less_than produces correct comparison results."""

    def _run_compare(self, n, a_val, b_val):
        # Layout: a(n) + b(n) + result(1) + ancilla(n)
        input_bits = {}
        a_bits = int_to_bits(a_val, n)
        b_bits = int_to_bits(b_val, n)
        for i in range(n):
            if a_bits[i]:
                input_bits[i] = 1
            if b_bits[i]:
                input_bits[n + i] = 1

        prog = less_than.build_exact(("a", n), ("b", n), ("result", 1))
        ir = lower_exact_program(prog)
        qc = QiskitBackend().emit(ir)

        from qiskit import QuantumCircuit
        prep = QuantumCircuit(qc.num_qubits)
        for idx in input_bits:
            prep.x(idx)
        qc = prep.compose(qc)

        sv = Statevector.from_instruction(qc)
        probs = sv.probabilities_dict()
        outcomes = {k: v for k, v in probs.items() if v > 0.99}
        assert len(outcomes) == 1
        result_str = list(outcomes.keys())[0]

        # result qubit is at position 2*n (after a and b)
        result_bit = int(result_str[-(2 * n + 1)])
        # Check a and b are preserved
        a_out = _bits_to_int(result_str, 0, n)
        b_out = _bits_to_int(result_str, n, n)
        return a_out, b_out, result_bit

    def test_2_lt_5(self):
        a_out, b_out, result = self._run_compare(3, 2, 5)
        assert a_out == 2
        assert b_out == 5
        assert result == 1  # 2 < 5

    def test_5_not_lt_2(self):
        a_out, b_out, result = self._run_compare(3, 5, 2)
        assert a_out == 5
        assert b_out == 2
        assert result == 0  # 5 >= 2

    def test_3_not_lt_3(self):
        a_out, b_out, result = self._run_compare(3, 3, 3)
        assert a_out == 3
        assert b_out == 3
        assert result == 0  # 3 == 3, not less than

    def test_0_lt_1(self):
        a_out, b_out, result = self._run_compare(2, 0, 1)
        assert a_out == 0
        assert b_out == 1
        assert result == 1

    def test_0_not_lt_0(self):
        a_out, b_out, result = self._run_compare(2, 0, 0)
        assert result == 0

    def test_all_pairs_3bit(self):
        """Exhaustive test: all 8x8 pairs for 3-bit comparator."""
        for a in range(8):
            for b in range(8):
                _, _, result = self._run_compare(3, a, b)
                expected = 1 if a < b else 0
                assert result == expected, f"Failed: {a} < {b} = {result}, expected {expected}"


# -----------------------------------------------------------------------
# apply_pattern_x_wires
# -----------------------------------------------------------------------

class TestPatternMatchCorrectness:
    """Verify apply_pattern_x_wires flips target for correct pattern."""

    def _make_pattern_match(self, pattern):
        n = len(pattern)

        @coherent
        def match(ctrl: QReg, tgt: QReg):
            apply_pattern_x_wires(ctrl.wires(), pattern, tgt[0])

        return match

    def test_pattern_11_matches_11(self):
        match = self._make_pattern_match([1, 1])
        # ctrl=11, tgt=0 → tgt should flip to 1
        result = _simulate(match, (("ctrl", 2), ("tgt", 1)),
                          input_bits={0: 1, 1: 1})
        tgt = int(result[-3])  # qubit 2
        assert tgt == 1

    def test_pattern_11_no_match_10(self):
        match = self._make_pattern_match([1, 1])
        # ctrl=10 (qubit0=0, qubit1=1), pattern needs 11 → no match
        result = _simulate(match, (("ctrl", 2), ("tgt", 1)),
                          input_bits={1: 1})
        tgt = int(result[-3])
        assert tgt == 0

    def test_pattern_01_matches_01(self):
        match = self._make_pattern_match([0, 1])
        # ctrl=01 (qubit0=0, qubit1=1), pattern [0,1] → match
        result = _simulate(match, (("ctrl", 2), ("tgt", 1)),
                          input_bits={1: 1})
        tgt = int(result[-3])
        assert tgt == 1
