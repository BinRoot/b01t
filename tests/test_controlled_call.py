"""Tests for the controlled_call utility."""

from b01t import (
    QReg,
    QiskitBackend,
    coherent,
    parametric,
    h,
    x,
    z,
    cx,
    ccx,
    lower_exact_program,
)
from b01t.kit import ancilla, compute, phase, uncompute, controlled_call
from b01t.zoo.grover import make_phase_oracle
from b01t.zoo.amplitude_amplification import make_amplification_step


# -----------------------------------------------------------------------
# Simple @coherent functions to control
# -----------------------------------------------------------------------

@coherent
def single_x(sys: QReg):
    x(sys[0])


@coherent
def two_cx(sys: QReg):
    cx(sys[0], sys[1])


@coherent
def hadamard_prep(sys: QReg):
    for q in sys:
        h(q)


oracle_11 = make_phase_oracle([1, 1])


# -----------------------------------------------------------------------
# Tests
# -----------------------------------------------------------------------

class TestControlledSingleGate:
    def test_controlled_x_compiles(self):
        """controlled_call on single X should produce a circuit with CX."""
        @parametric
        def wrapper(ctrl: QReg, sys: QReg):
            controlled_call(ctrl[0], single_x, sys)

        ir = wrapper.build(("ctrl", 1), ("sys", 1))
        qc = QiskitBackend().emit(ir)
        assert qc.num_qubits == 2

    def test_controlled_cx_compiles(self):
        """controlled_call on CX should produce CCX."""
        @parametric
        def wrapper(ctrl: QReg, sys: QReg):
            controlled_call(ctrl[0], two_cx, sys)

        ir = wrapper.build(("ctrl", 1), ("sys", 2))
        qc = QiskitBackend().emit(ir)
        assert qc.num_qubits == 3


class TestControlledHadamard:
    def test_controlled_h_compiles(self):
        """controlled_call on H gates should decompose and compile."""
        @parametric
        def wrapper(ctrl: QReg, sys: QReg):
            controlled_call(ctrl[0], hadamard_prep, sys)

        ir = wrapper.build(("ctrl", 1), ("sys", 2))
        qc = QiskitBackend().emit(ir)
        assert qc.num_qubits == 3
        assert qc.size() > 0


class TestControlledWithAncilla:
    def test_controlled_phase_oracle(self):
        """Phase oracle uses ancilla; controlled_call should flatten and compile."""
        oracle_101 = make_phase_oracle([1, 0, 1])

        @parametric
        def wrapper(ctrl: QReg, sys: QReg):
            controlled_call(ctrl[0], oracle_101, sys)

        ir = wrapper.build(("ctrl", 1), ("sys", 3))
        qc = QiskitBackend().emit(ir)
        # sys(3) + ctrl(1) + ancilla(1) from the oracle
        assert qc.num_qubits >= 4
        assert qc.size() > 0


class TestControlledGroverIterate:
    def test_controlled_grover_step(self):
        """Controlled Grover iterate (the key building block for coherent AE)."""
        grover = make_amplification_step(hadamard_prep, oracle_11)

        @parametric
        def wrapper(ctrl: QReg, sys: QReg):
            controlled_call(ctrl[0], grover, sys)

        ir = wrapper.build(("ctrl", 1), ("sys", 2))
        qc = QiskitBackend().emit(ir)
        assert qc.num_qubits >= 3
        assert qc.size() > 0

    def test_two_controlled_calls(self):
        """Two controlled Grover iterates (G^2 controlled on same qubit)."""
        grover = make_amplification_step(hadamard_prep, oracle_11)

        @parametric
        def wrapper(ctrl: QReg, sys: QReg):
            controlled_call(ctrl[0], grover, sys)
            controlled_call(ctrl[0], grover, sys)

        ir = wrapper.build(("ctrl", 1), ("sys", 2))
        qc = QiskitBackend().emit(ir)
        assert qc.num_qubits >= 3

    def test_different_control_qubits(self):
        """Controlled on different counting qubits (QPE pattern)."""
        grover = make_amplification_step(hadamard_prep, oracle_11)

        @parametric
        def wrapper(counting: QReg, sys: QReg):
            # QPE-like: G^1 controlled on counting[0], G^2 on counting[1]
            controlled_call(counting[0], grover, sys)
            controlled_call(counting[1], grover, sys)
            controlled_call(counting[1], grover, sys)

        ir = wrapper.build(("counting", 2), ("sys", 2))
        qc = QiskitBackend().emit(ir)
        assert qc.num_qubits >= 4
