"""Tests for the epidemic (SIR) rollout oracle.

Concrete qubit/gate counts match the b01t compiled oracle.
The paper (Table 4) reports Qiskit-reference counts which differ
because the b01t binary rank-select and ancilla coalescing produce
a different decomposition.
"""
from b01t import (
    QiskitBackend,
    Certification,
    lower_exact_program,
)

from demos.rollout.epidemic.epidemic_spec import EpidemicSpec
from demos.rollout.epidemic import (
    make_sir_transition,
    make_epidemic_terminal_eval,
    make_epidemic_rollout_oracle,
)


def _compile(oracle, spec):
    prog = oracle.build_exact(*spec.register_specs())
    ir = lower_exact_program(prog)
    qc = QiskitBackend().emit(ir)
    return prog, qc


class TestEpidemicSpec:
    def test_3x3_defaults(self):
        spec = EpidemicSpec()
        assert spec.n_cells == 9
        assert spec.n_susceptible_initially == 8
        assert spec.die_width == 3
        assert spec.infection_threshold(0) == 0
        assert spec.infection_threshold(1) == 2
        assert spec.recovery_threshold() == 2

    def test_register_specs_3x3_h1(self):
        spec = EpidemicSpec()
        specs = spec.register_specs()
        names = [name for name, _ in specs]
        assert "inf_work" in names
        assert "rem_work" in names
        assert "occ_work" in names
        assert "inf_1" in names
        assert "rem_1" in names
        assert "payoff" in names

    def test_2x2_h1(self):
        spec = EpidemicSpec(rows=2, cols=2, initial_infected=(0,), threshold=1)
        assert spec.n_cells == 4
        assert spec.n_susceptible_initially == 3


class TestSIRTransition:
    def test_is_safe(self):
        spec = EpidemicSpec(rows=2, cols=2, initial_infected=(0,), threshold=1)
        sir = make_sir_transition(spec)
        n = spec.n_cells
        prog = sir.build_exact(
            ("inf_src", n), ("rem_src", n),
            ("inf_dst", n), ("rem_dst", n),
            ("dice", spec.die_width * n),
        )
        assert prog.certification == Certification.SAFE

    def test_compiles_to_qiskit(self):
        spec = EpidemicSpec(rows=2, cols=2, initial_infected=(0,), threshold=1)
        sir = make_sir_transition(spec)
        n = spec.n_cells
        prog = sir.build_exact(
            ("inf_src", n), ("rem_src", n),
            ("inf_dst", n), ("rem_dst", n),
            ("dice", spec.die_width * n),
        )
        ir = lower_exact_program(prog)
        qc = QiskitBackend().emit(ir)
        assert qc.num_qubits > 0
        assert qc.size() > 0


class TestTerminalEval:
    def test_is_safe(self):
        spec = EpidemicSpec(rows=2, cols=2, initial_infected=(0,), threshold=1)
        term = make_epidemic_terminal_eval(spec)
        prog = term.build_exact(("inf", spec.n_cells), ("payoff", 1))
        assert prog.certification == Certification.SAFE

    def test_compiles_to_qiskit(self):
        spec = EpidemicSpec(rows=2, cols=2, initial_infected=(0,), threshold=1)
        term = make_epidemic_terminal_eval(spec)
        prog = term.build_exact(("inf", spec.n_cells), ("payoff", 1))
        ir = lower_exact_program(prog)
        qc = QiskitBackend().emit(ir)
        assert qc.num_qubits >= 5


class TestEpidemicCosts:
    """Verify compiled oracle costs match expected values."""

    def test_2x2_h1(self):
        spec = EpidemicSpec(rows=2, cols=2, initial_infected=(0,), threshold=1)
        oracle = make_epidemic_rollout_oracle(spec)
        prog, qc = _compile(oracle, spec)
        assert prog.certification == Certification.SAFE
        assert qc.num_qubits == 46
        assert qc.size() == 1343

    def test_3x3_h1(self):
        spec = EpidemicSpec()  # 3x3, center infected, T=2
        oracle = make_epidemic_rollout_oracle(spec)
        prog, qc = _compile(oracle, spec)
        assert prog.certification == Certification.SAFE
        assert qc.num_qubits == 91
        assert qc.size() == 4178

    def test_3x3_h2(self):
        spec = EpidemicSpec(horizon=2)  # 3x3, center infected, T=2, H=2
        oracle = make_epidemic_rollout_oracle(spec)
        prog, qc = _compile(oracle, spec)
        assert prog.certification == Certification.SAFE
        assert qc.num_qubits == 146
        assert qc.size() == 8560

    def test_5x5_h1(self):
        spec = EpidemicSpec(rows=5, cols=5, horizon=1, threshold=1,
                            initial_infected=(12,))
        oracle = make_epidemic_rollout_oracle(spec)
        prog, qc = _compile(oracle, spec)
        assert prog.certification == Certification.SAFE
        assert qc.num_qubits == 227
        assert qc.size() == 15322
