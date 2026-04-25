"""Tests for the Sway rollout oracle and its sub-components.

Qubit counts here match paper Tables 1 and 2; b01t is the source of truth.
"""
from b01t import (
    PackageMeta,
    PackageRegistry,
    QiskitBackend,
    Certification,
    lower_exact_program,
)
from b01t.zoo.rank_select import rank_select

from demos.rollout.sway.sway_spec import SwaySpec
from demos.rollout.sway import make_sway_transition, make_terminal_eval, make_rollout_oracle


def _compile(oracle, spec):
    prog = oracle.build_exact(*spec.register_specs())
    ir = lower_exact_program(prog)
    qc = QiskitBackend().emit(ir)
    return prog, qc


class TestSwaySpec:

    def test_register_specs_2x2_h1(self):
        spec = SwaySpec(rows=2, cols=2, horizon=1)
        specs = spec.register_specs()
        names = [name for name, _ in specs]
        assert "occ" in names
        assert "color_0" in names
        assert "color_1" in names
        assert "move_b1" in names
        assert "move_w1" in names
        assert "payoff" in names
        assert "same" not in names
        assert "cnt" not in names
        assert "black_sum" not in names

    def test_register_specs_5x5_h3(self):
        spec = SwaySpec(rows=5, cols=5, horizon=3)
        specs = spec.register_specs()
        names = [name for name, _ in specs]
        for i in range(4):
            assert f"color_{i}" in names
        for h in range(1, 4):
            assert f"move_b{h}" in names
            assert f"move_w{h}" in names
            assert f"sel_b{h}" in names
            assert f"sel_w{h}" in names
            assert f"dice_{h}" in names

    def test_qubit_count_5x5_h3(self):
        spec = SwaySpec(rows=5, cols=5, horizon=3)
        assert spec.total_qubits_estimate == 561


class TestComponentBuilds:

    def test_rank_select_is_safe(self):
        n, sel_w = 4, 2
        prog = rank_select.build_exact(("occ", n), ("selector", sel_w), ("target", n))
        assert prog.certification == Certification.SAFE

    def test_sway_transition_is_safe(self):
        spec = SwaySpec(rows=2, cols=2, horizon=1)
        sway = make_sway_transition(spec)
        n = spec.n_cells
        prog = sway.build_exact(
            ("occ", n), ("color_src", n), ("color_dst", n),
            ("dice", spec.die_width * n),
        )
        assert prog.certification == Certification.SAFE

    def test_terminal_eval_is_safe(self):
        spec = SwaySpec(rows=2, cols=2, horizon=1)
        term = make_terminal_eval(spec)
        n = spec.n_cells
        prog = term.build_exact(("occ", n), ("color", n), ("payoff", 1))
        assert prog.certification == Certification.SAFE


class TestSwayCosts:
    """Verify compiled oracle costs match expected values."""

    def test_2x2_h1(self):
        spec = SwaySpec(rows=2, cols=2, horizon=1)
        oracle = make_rollout_oracle(spec)
        prog, qc = _compile(oracle, spec)
        assert prog.certification == Certification.SAFE
        assert qc.num_qubits == 51
        assert qc.size() == 1895

    def test_3x3_h1(self):
        spec = SwaySpec(rows=3, cols=3, horizon=1)
        oracle = make_rollout_oracle(spec)
        prog, qc = _compile(oracle, spec)
        assert prog.certification == Certification.SAFE
        assert qc.num_qubits == 101
        assert qc.size() == 5542

    def test_3x3_h2(self):
        spec = SwaySpec(rows=3, cols=3, horizon=2)
        oracle = make_rollout_oracle(spec)
        prog, qc = _compile(oracle, spec)
        assert prog.certification == Certification.SAFE
        assert qc.num_qubits == 169
        assert qc.size() == 9768

    def test_5x5_h1(self):
        spec = SwaySpec(rows=5, cols=5, horizon=1)
        oracle = make_rollout_oracle(spec)
        prog, qc = _compile(oracle, spec)
        assert prog.certification == Certification.SAFE
        assert qc.num_qubits == 237
        assert qc.size() == 22265


class TestRolloutOracle5x5:

    def test_is_safe(self):
        spec = SwaySpec(rows=5, cols=5, horizon=3)
        oracle = make_rollout_oracle(spec)
        prog = oracle.build_exact(*spec.register_specs())
        assert prog.certification == Certification.SAFE

    def test_declared_qubit_count(self):
        spec = SwaySpec(rows=5, cols=5, horizon=3)
        oracle = make_rollout_oracle(spec)
        prog = oracle.build_exact(*spec.register_specs())
        total = sum(r.size for r in prog.regs)
        assert total >= 561

    def test_compiles_to_qiskit(self):
        spec = SwaySpec(rows=5, cols=5, horizon=3)
        oracle = make_rollout_oracle(spec)
        prog = oracle.build_exact(*spec.register_specs())
        ir = lower_exact_program(prog)
        qc = QiskitBackend().emit(ir)
        assert qc.num_qubits > 0
        assert qc.size() > 0


class TestDependencyResolution:

    def test_resolve_rollout_oracle(self):
        reg = PackageRegistry()
        reg.publish(PackageMeta(
            name="controlled_arithmetic",
            effect="coherent", safe=True, depends_on=[],
        ))
        reg.publish(PackageMeta(
            name="rank_select",
            effect="coherent", safe=True,
            depends_on=["controlled_arithmetic"],
        ))
        reg.publish(PackageMeta(
            name="sway_transition",
            effect="coherent", safe=True,
            depends_on=["controlled_arithmetic"],
        ))
        reg.publish(PackageMeta(
            name="terminal_eval",
            effect="coherent", safe=True,
            depends_on=["controlled_arithmetic"],
        ))
        reg.publish(PackageMeta(
            name="rollout_oracle",
            effect="coherent", safe=True,
            depends_on=["rank_select", "sway_transition", "terminal_eval"],
        ))

        chain = reg.resolve("rollout_oracle")
        names = [p.name for p in chain]
        assert names[-1] == "rollout_oracle"
        assert "controlled_arithmetic" in names
        assert "rank_select" in names
        assert names.index("controlled_arithmetic") < names.index("rank_select")
