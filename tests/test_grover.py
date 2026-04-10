"""Tests for Grover search oracle and its sub-components."""
from b01t import (
    PackageMeta,
    PackageRegistry,
    QReg,
    QiskitBackend,
    Certification,
    adaptive,
    parametric,
    coherent,
    ancilla,
    compute,
    h,
    measure_all,
    phase,
    repeat,
    x,
    z,
    ccx,
    cz,
    uncompute,
    lower_exact_program,
    exact_program_to_json,
    exact_program_from_json,
)


@coherent
def oracle(sys: QReg):
    with ancilla(1) as anc:
        compute(lambda: ccx(sys[0], sys[1], anc[0]))
        phase(lambda: z(anc[0]))
        uncompute()


@coherent
def diffusion_3q(sys: QReg):
    for q in sys.wires():
        h(q)
        x(q)
    with ancilla(1) as anc:
        compute(lambda: ccx(sys[0], sys[1], anc[0]))
        phase(lambda: cz(anc[0], sys[2]))
        uncompute()
    for q in sys.wires():
        x(q)
        h(q)


@coherent
def grover_step(sys: QReg):
    oracle(sys)
    diffusion_3q(sys)


@parametric
def grover_step_broad(sys: QReg):
    with ancilla(1) as anc:
        compute(lambda: ccx(sys[0], sys[1], anc[0]))
        phase(lambda: z(anc[0]))
        uncompute()
    for q in sys.wires():
        h(q)
        x(q)
    with ancilla(1) as anc:
        compute(lambda: ccx(sys[0], sys[1], anc[0]))
        phase(lambda: cz(anc[0], sys[2]))
        uncompute()
    for q in sys.wires():
        x(q)
        h(q)


@adaptive
def grover_search(sys: QReg):
    for q in sys.wires():
        h(q)
    repeat(2, lambda: grover_step_broad(sys))
    return measure_all(sys)


class TestExactOracle:
    def test_oracle_is_safe(self):
        prog = oracle.build_exact(("sys", 3))
        assert prog.certification == Certification.SAFE

    def test_oracle_has_ancilla(self):
        prog = oracle.build_exact(("sys", 3))
        assert any(r.kind == "anc" for r in prog.regs)

    def test_grover_step_is_safe(self):
        prog = grover_step.build_exact(("sys", 3))
        assert prog.certification == Certification.SAFE


class TestSerialization:
    def test_round_trip(self):
        prog = oracle.build_exact(("sys", 3))
        json_str = exact_program_to_json(prog)
        restored = exact_program_from_json(json_str)
        assert restored.name == prog.name
        assert len(restored.ops) == len(prog.ops)


class TestQiskitCompilation:
    def test_oracle_compiles(self):
        prog = oracle.build_exact(("sys", 3))
        ir = lower_exact_program(prog)
        qc = QiskitBackend().emit(ir)
        assert qc.num_qubits > 0
        assert qc.size() > 0

    def test_grover_step_compiles(self):
        prog = grover_step.build_exact(("sys", 3))
        ir = lower_exact_program(prog)
        qc = QiskitBackend().emit(ir)
        assert qc.num_qubits > 0


class TestBroadPath:
    def test_grover_search_builds(self):
        ir = grover_search.build(("sys", 3))
        assert not ir.is_safe  # @adaptive has measurement
        assert len(ir.ops) > 0

    def test_grover_search_compiles(self):
        ir = grover_search.build(("sys", 3))
        qc = QiskitBackend().emit(ir)
        assert qc.num_qubits > 0


class TestRegistry:
    def test_publish_exact_artifact(self):
        prog = oracle.build_exact(("sys", 3))
        ir = lower_exact_program(prog)
        reg = PackageRegistry()
        reg.publish(PackageMeta(
            name="oracle.and_mark",
            effect="coherent",
            safe=True,
            tags=["oracle", "exact", "grover-compatible"],
            ir=ir,
            exact_program=prog,
        ))
        assert reg.get("oracle.and_mark") is not None
        assert "exact" in reg.find_by_tag("exact")[0].tags
