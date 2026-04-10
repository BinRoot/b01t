"""Tests for amplitude amplification zoo module."""
from b01t import (
    QReg,
    QiskitBackend,
    Certification,
    coherent,
    h,
    x,
    z,
    ccx,
    lower_exact_program,
)
from b01t.kit import ancilla, compute, phase, uncompute
from b01t.zoo.grover import make_phase_oracle
from b01t.zoo.amplitude_amplification import (
    make_amplification_step,
    make_amplitude_amplifier,
)


# State prep: uniform superposition (standard Grover)
@coherent
def hadamard_prep(sys: QReg):
    for q in sys:
        h(q)


# Oracle: marks |11> (reuse from zoo)
oracle_11 = make_phase_oracle([1, 1])


class TestAmplificationStep:
    def test_is_safe(self):
        step = make_amplification_step(hadamard_prep, oracle_11)
        prog = step.build_exact(("sys", 2))
        assert prog.certification == Certification.SAFE

    def test_compiles_to_qiskit(self):
        step = make_amplification_step(hadamard_prep, oracle_11)
        prog = step.build_exact(("sys", 2))
        ir = lower_exact_program(prog)
        qc = QiskitBackend().emit(ir)
        assert qc.num_qubits > 0

    def test_3qubit_oracle(self):
        oracle_101 = make_phase_oracle([1, 0, 1])
        step = make_amplification_step(hadamard_prep, oracle_101)
        prog = step.build_exact(("sys", 3))
        assert prog.certification == Certification.SAFE


class TestAmplitudeAmplifier:
    def test_single_iteration(self):
        amp = make_amplitude_amplifier(hadamard_prep, oracle_11, num_iterations=1)
        prog = amp.build_exact(("sys", 2))
        assert prog.certification == Certification.SAFE

    def test_two_iterations(self):
        amp = make_amplitude_amplifier(hadamard_prep, oracle_11, num_iterations=2)
        prog = amp.build_exact(("sys", 2))
        assert prog.certification == Certification.SAFE

    def test_compiles_to_qiskit(self):
        amp = make_amplitude_amplifier(hadamard_prep, oracle_11, num_iterations=2)
        prog = amp.build_exact(("sys", 2))
        ir = lower_exact_program(prog)
        qc = QiskitBackend().emit(ir)
        assert qc.num_qubits > 0
        assert qc.size() > 0

    def test_custom_oracle(self):
        """Amplitude amplification with a custom ancilla-based oracle."""
        @coherent
        def custom_oracle(sys: QReg):
            """Marks |110> via ancilla discipline."""
            with ancilla(1) as anc:
                compute(lambda: (x(sys[2]), ccx(sys[0], sys[1], anc[0])))
                phase(lambda: z(anc[0]))
                uncompute()

        amp = make_amplitude_amplifier(hadamard_prep, custom_oracle, num_iterations=1)
        prog = amp.build_exact(("sys", 3))
        assert prog.certification == Certification.SAFE

    def test_zero_iterations_is_just_prep(self):
        """Zero iterations = just state prep, no amplification."""
        amp = make_amplitude_amplifier(hadamard_prep, oracle_11, num_iterations=0)
        prog = amp.build_exact(("sys", 2))
        assert prog.certification == Certification.SAFE
