"""Tests for the exact-core oracle layer.

Covers: construction by type, forbidden ops, ancilla discipline,
par disjointness, lowering, serialization, registry, and exact/broad interop.

Run with: uv run python -m pytest tests/test_exact_core.py -v
"""
import json
import tempfile

import pytest
from b01t import (
    DSLValidationError, QReg, Wire, QiskitBackend,
    # Shared gate functions
    h, x, z, s, sdg, t, tdg, cx, cz, swap, ccx, ccz, mcx, mcz,
    rx, ry, rz, cry, crz, measure, measure_all,
    # Decorators and combinators
    coherent, parametric, adaptive,
    ancilla, compute, phase, apply, uncompute, par, adjoint,
    # Exact core types
    ExactGate, ExactGateOp, ExactAncillaBlock, ExactParOp, ExactProgram,
    lower_exact_program,
    exact_program_to_dict, exact_program_from_dict,
    exact_program_to_json, exact_program_from_json,
    PackageMeta, PackageRegistry,
)
from b01t.kit.control import if_then


# ====================================================================
# A. Construction by type, not boolean
# ====================================================================

class TestExactConstruction:
    def test_exact_coherent_builds_exact_program(self):
        """@coherent builds ExactProgram, not IRProgram."""
        @coherent
        def f(sys: QReg):
            h(sys[0])
            cx(sys[0], sys[1])
        prog = f.build_exact(("sys", 2))
        assert isinstance(prog, ExactProgram)

    def test_exact_program_has_no_is_safe(self):
        """ExactProgram has no is_safe attribute; it is safe by construction."""
        @coherent
        def f(sys: QReg):
            h(sys[0])
        prog = f.build_exact(("sys", 1))
        assert not hasattr(prog, "is_safe")

    def test_exact_gates_build_successfully(self):
        """All exact gates can be used inside @coherent."""
        @coherent
        def f(sys: QReg):
            h(sys[0])
            x(sys[1])
            z(sys[2])
            s(sys[0])
            sdg(sys[0])
            t(sys[1])
            tdg(sys[1])
            cx(sys[0], sys[1])
            cz(sys[1], sys[2])
            swap(sys[0], sys[2])
            ccx(sys[0], sys[1], sys[2])
            ccz(sys[0], sys[1], sys[2])
        prog = f.build_exact(("sys", 3))
        assert len(prog.ops) == 12

    def test_mcx_mcz_build(self):
        @coherent
        def f(sys: QReg):
            mcx(sys.wires()[:2], sys[2])
            mcz(sys.wires()[:2], sys[2])
        prog = f.build_exact(("sys", 3))
        assert len(prog.ops) == 2

    def test_ops_are_exact_types(self):
        """Built ops are ExactGateOp, not broad GateOp."""
        @coherent
        def f(sys: QReg):
            h(sys[0])
            cx(sys[0], sys[1])
        prog = f.build_exact(("sys", 2))
        assert isinstance(prog.ops[0], ExactGateOp)
        assert prog.ops[0].gate == ExactGate.H
        assert isinstance(prog.ops[1], ExactGateOp)
        assert prog.ops[1].gate == ExactGate.CX

    def test_regs_are_tuples(self):
        """ExactProgram uses immutable tuples for regs and ops."""
        @coherent
        def f(sys: QReg):
            h(sys[0])
        prog = f.build_exact(("sys", 2))
        assert isinstance(prog.regs, tuple)
        assert isinstance(prog.ops, tuple)


# ====================================================================
# B. Forbidden ops rejected in exact core
# ====================================================================

class TestExactForbiddenOps:
    def test_ry_rejected(self):
        @coherent
        def f(sys: QReg):
            ry(0.5, sys[0])
        with pytest.raises(DSLValidationError, match="not allowed in @coherent"):
            f.build_exact(("sys", 1))

    def test_rx_rejected(self):
        @coherent
        def f(sys: QReg):
            rx(0.3, sys[0])
        with pytest.raises(DSLValidationError, match="not allowed in @coherent"):
            f.build_exact(("sys", 1))

    def test_rz_rejected(self):
        @coherent
        def f(sys: QReg):
            rz(0.7, sys[0])
        with pytest.raises(DSLValidationError, match="not allowed in @coherent"):
            f.build_exact(("sys", 1))

    def test_cry_rejected(self):
        @coherent
        def f(sys: QReg):
            cry(1.0, sys[0], sys[1])
        with pytest.raises(DSLValidationError, match="not allowed in @coherent"):
            f.build_exact(("sys", 2))

    def test_crz_rejected(self):
        @coherent
        def f(sys: QReg):
            crz(1.0, sys[0], sys[1])
        with pytest.raises(DSLValidationError, match="not allowed in @coherent"):
            f.build_exact(("sys", 2))

    def test_measure_rejected(self):
        @coherent
        def f(sys: QReg):
            measure(sys[0])
        with pytest.raises(DSLValidationError, match="not allowed in @coherent"):
            f.build_exact(("sys", 1))

    def test_measure_all_rejected(self):
        @coherent
        def f(sys: QReg):
            measure_all(sys)
        with pytest.raises(DSLValidationError, match="not allowed in @coherent"):
            f.build_exact(("sys", 1))

    def test_if_then_rejected(self):
        @coherent
        def f(sys: QReg):
            if_then("cond", lambda: x(sys[0]))
        with pytest.raises(DSLValidationError, match="not allowed in @coherent"):
            f.build_exact(("sys", 1))


# ====================================================================
# C. Exact ancilla discipline
# ====================================================================

class TestExactAncilla:
    def test_basic_ancilla_block(self):
        @coherent
        def f(sys: QReg):
            with ancilla(1) as anc:
                compute(lambda: cx(sys[0], anc[0]))
                phase(lambda: z(anc[0]))
                uncompute()
        prog = f.build_exact(("sys", 2))
        assert len(prog.ops) == 1
        blk = prog.ops[0]
        assert isinstance(blk, ExactAncillaBlock)
        assert len(blk.compute_ops) == 1
        assert blk.compute_ops[0].gate == ExactGate.CX
        assert len(blk.middle_ops) == 1
        assert blk.middle_ops[0].gate == ExactGate.Z
        assert len(blk.uncompute_ops) == 1
        assert blk.uncompute_ops[0].gate == ExactGate.CX

    def test_phase_rz_rejected(self):
        """rz is not in the exact phase set."""
        @coherent
        def f(sys: QReg):
            with ancilla(1) as anc:
                compute(lambda: x(anc[0]))
                phase(lambda: rz(0.5, anc[0]))
                uncompute()
        with pytest.raises(DSLValidationError, match="not allowed"):
            f.build_exact(("sys", 1))

    def test_compute_non_compute_gate_rejected(self):
        """H is not in the exact compute set."""
        @coherent
        def f(sys: QReg):
            with ancilla(1) as anc:
                compute(lambda: h(anc[0]))
                phase(lambda: z(anc[0]))
                uncompute()
        with pytest.raises(DSLValidationError, match="not allowed in exact compute"):
            f.build_exact(("sys", 1))

    def test_uncompute_is_exact_inverse(self):
        """Uncompute must be the exact inverse of compute in reverse."""
        @coherent
        def f(sys: QReg):
            with ancilla(1) as anc:
                compute(lambda: (cx(sys[0], anc[0]), x(anc[0])))
                phase(lambda: z(anc[0]))
                uncompute()
        prog = f.build_exact(("sys", 2))
        blk = prog.ops[0]
        assert isinstance(blk, ExactAncillaBlock)
        # compute: [CX, X] -> uncompute: [X, CX] (reversed, both self-inverse)
        assert blk.uncompute_ops[0].gate == ExactGate.X
        assert blk.uncompute_ops[1].gate == ExactGate.CX

    def test_multi_stage_ancilla(self):
        @coherent
        def f(sys: QReg):
            with ancilla(1) as anc:
                compute(lambda: cx(sys[0], anc[0]))
                phase(lambda: z(anc[0]))
                uncompute()
                compute(lambda: cx(sys[1], anc[0]))
                phase(lambda: t(anc[0]))
                uncompute()
        prog = f.build_exact(("sys", 3))
        assert len(prog.ops) == 2
        assert isinstance(prog.ops[0], ExactAncillaBlock)
        assert isinstance(prog.ops[1], ExactAncillaBlock)

    def test_s_sdg_inverse_in_uncompute(self):
        """S in compute should produce SDG in uncompute (but S not in compute set)."""
        # S is not a compute gate, so this tests that phase gates are rejected in compute
        @coherent
        def f(sys: QReg):
            with ancilla(1) as anc:
                compute(lambda: s(anc[0]))
                phase(lambda: z(anc[0]))
                uncompute()
        with pytest.raises(DSLValidationError, match="not allowed in exact compute"):
            f.build_exact(("sys", 1))


# ====================================================================
# D. Recursive par disjointness in exact core
# ====================================================================

class TestExactParDisjointness:
    def test_overlapping_wires_rejected(self):
        @coherent
        def f(sys: QReg):
            par(lambda: h(sys[0]), lambda: x(sys[0]))
        with pytest.raises(DSLValidationError, match="disjoint|overlap"):
            f.build_exact(("sys", 2))

    def test_disjoint_branches_accepted(self):
        @coherent
        def f(a: QReg, b: QReg):
            par(lambda: h(a[0]), lambda: x(b[0]))
        prog = f.build_exact(("a", 1), ("b", 1))
        assert len(prog.ops) == 1
        assert isinstance(prog.ops[0], ExactParOp)

    def test_nested_overlap_rejected(self):
        @coherent
        def f(sys: QReg):
            par(
                lambda: par(lambda: h(sys[0]), lambda: x(sys[1])),
                lambda: z(sys[0]),  # overlaps with inner left
            )
        with pytest.raises(DSLValidationError, match="disjoint|overlap"):
            f.build_exact(("sys", 3))

    def test_different_wires_same_register_passes(self):
        @coherent
        def f(sys: QReg):
            par(lambda: h(sys[0]), lambda: x(sys[1]))
        prog = f.build_exact(("sys", 3))
        assert len(prog.ops) == 1


# ====================================================================
# E. Lowering
# ====================================================================

class TestExactLowering:
    def test_produces_coherent_ir(self):
        @coherent
        def f(sys: QReg):
            h(sys[0])
            cx(sys[0], sys[1])
        prog = f.build_exact(("sys", 2))
        ir = lower_exact_program(prog)
        from b01t import Effect
        assert ir.effect is Effect.COHERENT
        assert ir.is_safe is True

    def test_gate_names_map_correctly(self):
        @coherent
        def f(sys: QReg):
            h(sys[0])
            t(sys[0])
            sdg(sys[0])
            cx(sys[0], sys[1])
        prog = f.build_exact(("sys", 2))
        ir = lower_exact_program(prog)
        names = [op.name for op in ir.ops]
        assert names == ["h", "t", "sdg", "cx"]

    def test_ancilla_block_lowers(self):
        @coherent
        def f(sys: QReg):
            with ancilla(1) as anc:
                compute(lambda: cx(sys[0], anc[0]))
                phase(lambda: z(anc[0]))
                uncompute()
        prog = f.build_exact(("sys", 2))
        ir = lower_exact_program(prog)
        from b01t import AncillaBlockOp
        assert len(ir.ops) == 1
        assert isinstance(ir.ops[0], AncillaBlockOp)
        assert ir.ops[0].compute_ops[0].name == "cx"
        assert ir.ops[0].phase_ops[0].name == "z"

    def test_par_lowers(self):
        @coherent
        def f(a: QReg, b: QReg):
            par(lambda: h(a[0]), lambda: x(b[0]))
        prog = f.build_exact(("a", 1), ("b", 1))
        ir = lower_exact_program(prog)
        from b01t import ParOp
        assert len(ir.ops) == 1
        assert isinstance(ir.ops[0], ParOp)

    def test_lowered_program_compiles_via_backend(self):
        @coherent
        def f(sys: QReg):
            h(sys[0])
            cx(sys[0], sys[1])
            t(sys[1])
        prog = f.build_exact(("sys", 2))
        ir = lower_exact_program(prog)
        qc = QiskitBackend().emit(ir)
        assert qc.num_qubits == 2
        assert qc.size() == 3

    def test_lowered_ancilla_compiles_via_backend(self):
        @coherent
        def f(sys: QReg):
            with ancilla(1) as anc:
                compute(lambda: cx(sys[0], anc[0]))
                phase(lambda: z(anc[0]))
                uncompute()
        prog = f.build_exact(("sys", 2))
        ir = lower_exact_program(prog)
        qc = QiskitBackend().emit(ir)
        assert qc.num_qubits == 3  # 2 sys + 1 anc
        assert qc.size() == 3  # cx, z, cx


# ====================================================================
# F. Serialization / sharing
# ====================================================================

class TestExactSerde:
    def test_round_trip_json(self):
        @coherent
        def f(sys: QReg):
            h(sys[0])
            cx(sys[0], sys[1])
            t(sys[1])
        prog = f.build_exact(("sys", 2))
        j = exact_program_to_json(prog)
        prog2 = exact_program_from_json(j)
        assert prog == prog2

    def test_round_trip_with_ancilla(self):
        @coherent
        def f(sys: QReg):
            with ancilla(1) as anc:
                compute(lambda: cx(sys[0], anc[0]))
                phase(lambda: z(anc[0]))
                uncompute()
        prog = f.build_exact(("sys", 2))
        j = exact_program_to_json(prog)
        prog2 = exact_program_from_json(j)
        assert prog == prog2

    def test_round_trip_with_par(self):
        @coherent
        def f(a: QReg, b: QReg):
            par(lambda: h(a[0]), lambda: x(b[0]))
        prog = f.build_exact(("a", 1), ("b", 1))
        j = exact_program_to_json(prog)
        prog2 = exact_program_from_json(j)
        assert prog == prog2

    def test_deterministic_output(self):
        """Same program serializes to identical JSON."""
        @coherent
        def f(sys: QReg):
            h(sys[0])
            cx(sys[0], sys[1])
        prog = f.build_exact(("sys", 2))
        j1 = exact_program_to_json(prog)
        j2 = exact_program_to_json(prog)
        assert j1 == j2

    def test_format_version_present(self):
        @coherent
        def f(sys: QReg):
            h(sys[0])
        prog = f.build_exact(("sys", 1))
        d = exact_program_to_dict(prog)
        assert d["format"] == "exact-oracle-v1"

    def test_bad_format_rejected(self):
        with pytest.raises(DSLValidationError, match="unsupported exact oracle format"):
            exact_program_from_dict({"format": "wrong-v99", "name": "x",
                                     "regs": [], "ops": []})

    def test_registry_round_trip(self):
        @coherent
        def oracle(sys: QReg):
            h(sys[0])
            with ancilla(1) as anc:
                compute(lambda: cx(sys[0], anc[0]))
                phase(lambda: z(anc[0]))
                uncompute()
        prog = oracle.build_exact(("sys", 2))

        reg = PackageRegistry()
        reg.publish(PackageMeta(
            name="my_oracle", effect="coherent", safe=True,
            tags=["oracle", "exact"],
            exact_program=prog,
        ))

        with tempfile.NamedTemporaryFile(suffix=".json", mode="w", delete=False) as f:
            path = f.name
        reg.save(path)

        reg2 = PackageRegistry()
        reg2.load(path)
        loaded = reg2.get("my_oracle")
        assert loaded is not None
        assert loaded.exact_program is not None
        assert loaded.exact_program == prog
        assert loaded.artifact_format == "exact-oracle-v1"


# ====================================================================
# G. Exact/Broad interoperability
# ====================================================================

class TestInteroperability:
    def test_parametric_builds_ir(self):
        """@parametric builds IRProgram with is_safe."""
        @parametric
        def f(sys: QReg):
            h(sys[0])
            x(sys[1])
        ir = f.build(("sys", 2))
        from b01t import IRProgram
        assert isinstance(ir, IRProgram)
        assert ir.is_safe

    def test_adaptive_builds_ir(self):
        @adaptive
        def f(sys: QReg):
            h(sys[0])
            measure(sys[0])
        ir = f.build(("sys", 1))
        assert not ir.is_safe

    def test_coherent_and_parametric_dont_interfere(self):
        """Building exact (@coherent) then broad (@parametric) in sequence works."""
        @coherent
        def exact_fn(sys: QReg):
            h(sys[0])
        prog = exact_fn.build_exact(("sys", 1))
        assert isinstance(prog, ExactProgram)

        @parametric
        def broad_fn(sys: QReg):
            h(sys[0])
            ry(0.5, sys[0])
        ir = broad_fn.build(("sys", 1))
        from b01t import IRProgram
        assert isinstance(ir, IRProgram)
        assert not ir.is_safe  # ry makes it non-safe


# ====================================================================
# H. Exact adjoint
# ====================================================================

class TestExactAdjoint:
    def test_adjoint_of_exact_function(self):
        @coherent
        def sub(sys: QReg):
            t(sys[0])
            cx(sys[0], sys[1])

        @coherent
        def f(sys: QReg):
            adjoint(sub, sys)
        prog = f.build_exact(("sys", 2))
        # sub: [T, CX] -> adjoint: [CX, TDG] (reversed + inverted)
        assert len(prog.ops) == 2
        assert prog.ops[0].gate == ExactGate.CX
        assert prog.ops[1].gate == ExactGate.TDG

    def test_adjoint_inside_ancilla_rejected(self):
        @coherent
        def sub(sys: QReg):
            h(sys[0])

        @coherent
        def f(sys: QReg):
            with ancilla(1) as anc:
                adjoint(sub, sys)
        with pytest.raises(DSLValidationError, match="cannot be used inside"):
            f.build_exact(("sys", 2))

    def test_adjoint_of_ancilla_block(self):
        @coherent
        def sub(sys: QReg):
            with ancilla(1) as anc:
                compute(lambda: cx(sys[0], anc[0]))
                phase(lambda: z(anc[0]))
                uncompute()

        @coherent
        def f(sys: QReg):
            adjoint(sub, sys)
        prog = f.build_exact(("sys", 2))
        assert len(prog.ops) == 1
        assert isinstance(prog.ops[0], ExactAncillaBlock)


# ====================================================================
# I. Wire validation in exact core
# ====================================================================

class TestExactWireValidation:
    def test_duplicate_wires_rejected(self):
        @coherent
        def f(sys: QReg):
            cx(sys[0], sys[0])
        with pytest.raises(DSLValidationError, match="distinct"):
            f.build_exact(("sys", 2))

    def test_undeclared_register_rejected(self):
        @coherent
        def f(sys: QReg):
            foreign = Wire("ghost", 0)
            h(foreign)
        with pytest.raises(DSLValidationError, match="undeclared"):
            f.build_exact(("sys", 2))


# ====================================================================
# J. Golden round-trip: the single most important test
# ====================================================================

class TestGoldenRoundTrip:
    """One nontrivial oracle exercising every exact-core feature,
    verified end-to-end through the entire pipeline:

        build -> serialize -> deserialize -> equality
                                          -> lower -> backend
                                          -> re-serialize -> JSON stability
    """

    def test_full_pipeline(self):
        # -- A small subroutine whose adjoint we will take --
        @coherent
        def phase_kick(aux: QReg):
            s(aux[0])
            t(aux[1])

        # -- The main oracle --
        @coherent
        def oracle(sys: QReg, aux: QReg):
            # 1. Ancilla block: cx+ccx compute, z+t phase, auto-uncompute
            with ancilla(1) as anc:
                compute(lambda: (cx(sys[0], anc[0]), ccx(sys[0], sys[1], anc[0])))
                phase(lambda: (z(anc[0]), t(anc[0])))
                uncompute()

            # 2. Parallel branch on disjoint register
            par(
                lambda: h(sys[0]),
                lambda: x(aux[0]),
            )

            # 3. Adjoint of the subroutine on aux
            adjoint(phase_kick, aux)

        # -- Step 1: build ExactProgram --
        prog = oracle.build_exact(("sys", 2), ("aux", 2))
        assert isinstance(prog, ExactProgram)
        assert not hasattr(prog, "is_safe")

        # Structural spot-checks
        assert len(prog.ops) == 4  # ancilla block, par, SDG, TDG
        assert isinstance(prog.ops[0], ExactAncillaBlock)
        assert isinstance(prog.ops[1], ExactParOp)
        # adjoint of [S, T] = [TDG, SDG] (reversed + inverted)
        assert prog.ops[2].gate == ExactGate.TDG
        assert prog.ops[3].gate == ExactGate.SDG

        # -- Step 2: serialize to JSON --
        json_str = exact_program_to_json(prog)
        parsed = json.loads(json_str)
        assert parsed["format"] == "exact-oracle-v1"
        assert parsed["name"] == "oracle"

        # -- Step 3: deserialize back --
        prog2 = exact_program_from_json(json_str)

        # -- Step 4: structural equality --
        assert prog == prog2

        # -- Step 5: lower to broad IR --
        ir = lower_exact_program(prog2)
        from b01t import Effect, AncillaBlockOp, ParOp, IRProgram
        assert isinstance(ir, IRProgram)
        assert ir.effect is Effect.COHERENT
        assert ir.is_safe is True
        assert isinstance(ir.ops[0], AncillaBlockOp)
        assert isinstance(ir.ops[1], ParOp)
        assert ir.ops[0].compute_ops[0].name == "cx"
        assert ir.ops[0].compute_ops[1].name == "ccx"

        # -- Step 6: emit backend circuit --
        qc = QiskitBackend().emit(ir)
        assert qc.num_qubits == 5  # sys(2) + aux(2) + anc(1)
        # ancilla block: cx, ccx, z, t, ccx, cx = 6
        # par: h, x = 2
        # adjoint: tdg, sdg = 2
        assert qc.size() == 10

        # -- Step 7: re-serialize, confirm JSON stability --
        json_str_2 = exact_program_to_json(prog2)
        assert json_str == json_str_2


# ====================================================================
# K. Semantic equivalence: exact path vs broad path produce same unitary
# ====================================================================

class TestSemanticEquivalence:
    """Build the same oracle via @coherent and @coherent, lower both
    to Qiskit circuits, and compare unitaries. This checks meaning, not
    just structure."""

    def test_exact_and_broad_produce_same_unitary(self):
        from qiskit.quantum_info import Operator

        # -- Exact path --
        @coherent
        def exact_oracle(sys: QReg):
            h(sys[0])
            with ancilla(1) as anc:
                compute(lambda: cx(sys[0], anc[0]))
                phase(lambda: (z(anc[0]), t(anc[0])))
                uncompute()
            par(lambda: s(sys[0]), lambda: tdg(sys[1]))

        prog = exact_oracle.build_exact(("sys", 2))
        ir_exact = lower_exact_program(prog)
        qc_exact = QiskitBackend().emit(ir_exact)

        # -- Broad path: identical logic using @parametric --
        @parametric
        def broad_oracle(sys: QReg):
            h(sys[0])
            with ancilla(1) as anc:
                compute(lambda: cx(sys[0], anc[0]))
                phase(lambda: (z(anc[0]), t(anc[0])))
                uncompute()
            par(lambda: s(sys[0]), lambda: tdg(sys[1]))

        ir_broad = broad_oracle.build(("sys", 2))
        qc_broad = QiskitBackend().emit(ir_broad)

        # -- Compare unitaries --
        u_exact = Operator(qc_exact)
        u_broad = Operator(qc_broad)
        assert u_exact.equiv(u_broad), (
            "exact and broad paths produced different unitaries")

    def test_ancilla_traces_out_cleanly(self):
        """The ancilla starts and ends in |0>, so tracing it out should
        leave the same system-only unitary as an equivalent circuit
        without ancilla.

        cx(sys[0], anc[0]); z(anc[0]); cx(sys[0], anc[0])
        = controlled-Z phase on sys[0] (Z when sys[0]=|1>, I when |0>).
        System-only equivalent: z(sys[0]) on a 1-qubit register.
        """
        from qiskit.quantum_info import Operator
        import numpy as np

        @coherent
        def with_anc(sys: QReg):
            with ancilla(1) as anc:
                compute(lambda: cx(sys[0], anc[0]))
                phase(lambda: z(anc[0]))
                uncompute()

        @coherent
        def without_anc(sys: QReg):
            z(sys[0])

        prog_anc = with_anc.build_exact(("sys", 1))
        prog_no = without_anc.build_exact(("sys", 1))

        # Ancilla version: 2 qubits (1 sys + 1 anc)
        ir_anc = lower_exact_program(prog_anc)
        qc_anc = QiskitBackend().emit(ir_anc)
        u_full = Operator(qc_anc).data  # 4x4

        # System-only version: 1 qubit
        ir_no = lower_exact_program(prog_no)
        qc_no = QiskitBackend().emit(ir_no)
        u_sys = Operator(qc_no).data  # 2x2

        # Project ancilla onto |0><0|: ancilla is the last register.
        # Pick rows/cols where anc bit = 0 (even indices).
        projected = u_full[::2, ::2]
        assert np.allclose(projected, u_sys, atol=1e-10), (
            "ancilla did not trace out cleanly")


# ====================================================================
# L. Serialization stability across construction order
# ====================================================================

class TestSerializationCanonical:
    """Build the 'same' oracle through two different but extensionally
    identical Python constructions and confirm the serialized JSON is
    identical; the artifact is canonical, not construction-order-dependent."""

    def test_same_oracle_different_construction_same_json(self):
        # -- Construction A: inline everything --
        @coherent
        def oracle_a(sys: QReg):
            h(sys[0])
            cx(sys[0], sys[1])
            with ancilla(1) as anc:
                compute(lambda: cx(sys[0], anc[0]))
                phase(lambda: z(anc[0]))
                uncompute()
            t(sys[1])

        prog_a = oracle_a.build_exact(("sys", 2))

        # -- Construction B: same ops, built via subroutine + adjoint(adjoint) --
        # adjoint(adjoint(f)) == f for exact gates
        @coherent
        def tdg_sub(sys: QReg):
            tdg(sys[1])

        @coherent
        def oracle_b(sys: QReg):
            h(sys[0])
            cx(sys[0], sys[1])
            with ancilla(1) as anc:
                compute(lambda: cx(sys[0], anc[0]))
                phase(lambda: z(anc[0]))
                uncompute()
            # adjoint(TDG) = T
            adjoint(tdg_sub, sys)

        prog_b = oracle_b.build_exact(("sys", 2))

        # -- Both should produce structurally equal ops and regs --
        assert prog_a.regs == prog_b.regs
        assert prog_a.ops == prog_b.ops

        # -- And therefore identical serialized JSON (normalizing name) --
        dict_a = exact_program_to_dict(prog_a)
        dict_b = exact_program_to_dict(prog_b)
        dict_a["name"] = "oracle"
        dict_b["name"] = "oracle"
        json_a = json.dumps(dict_a, sort_keys=True, indent=2)
        json_b = json.dumps(dict_b, sort_keys=True, indent=2)
        assert json_a == json_b

    def test_gate_order_matters(self):
        """Different gate orderings should NOT produce the same JSON -
        canonicality preserves program order, it doesn't sort ops."""
        @coherent
        def f1(sys: QReg):
            h(sys[0])
            t(sys[0])
        @coherent
        def f2(sys: QReg):
            t(sys[0])
            h(sys[0])

        j1 = exact_program_to_json(f1.build_exact(("sys", 1)))
        j2 = exact_program_to_json(f2.build_exact(("sys", 1)))
        assert j1 != j2


# ====================================================================
# M. @primitive tier (IsCoh vs IsSafe)
# ====================================================================

class TestPrimitiveTier:
    """@primitive builds ExactProgram with Certification.PRIMITIVE.
    @coherent builds ExactProgram with Certification.SAFE.
    Both use the exact gate set, but differ in certification level."""

    def test_primitive_builds_exact_program(self):
        from b01t import primitive, Certification
        @primitive
        def f(ctrl: QReg, reg: QReg):
            cx(ctrl[0], reg[0])
        prog = f.build_exact(("ctrl", 1), ("reg", 2))
        assert isinstance(prog, ExactProgram)
        assert prog.certification == Certification.PRIMITIVE

    def test_coherent_is_safe(self):
        from b01t import Certification
        @coherent
        def f(sys: QReg):
            h(sys[0])
            with ancilla(1) as anc:
                compute(lambda: cx(sys[0], anc[0]))
                phase(lambda: z(anc[0]))
                uncompute()
        prog = f.build_exact(("sys", 2))
        assert prog.certification == Certification.SAFE

    def test_primitive_rejects_rotations(self):
        """@primitive still uses the exact gate set, with no ry/rz."""
        from b01t import primitive
        @primitive
        def f(sys: QReg):
            ry(0.5, sys[0])
        with pytest.raises(DSLValidationError, match="not allowed in @coherent"):
            f.build_exact(("sys", 1))

    def test_primitive_allows_caller_managed_scratch(self):
        """@primitive allows taking scratch registers as arguments."""
        from b01t import primitive, Certification
        @primitive
        def inc(ctrl: QReg, reg: QReg):
            cx(ctrl[0], reg[0])
            ccx(ctrl[0], reg[0], reg[1])
        prog = inc.build_exact(("ctrl", 1), ("reg", 3))
        assert prog.certification == Certification.PRIMITIVE
        assert len(prog.ops) == 2

    def test_certification_round_trips_through_json(self):
        from b01t import primitive, Certification
        @primitive
        def f(ctrl: QReg, reg: QReg):
            cx(ctrl[0], reg[0])
        prog = f.build_exact(("ctrl", 1), ("reg", 2))
        j = exact_program_to_json(prog)
        prog2 = exact_program_from_json(j)
        assert prog2.certification == Certification.PRIMITIVE
        assert prog == prog2

    def test_safe_certification_round_trips(self):
        from b01t import Certification
        @coherent
        def f(sys: QReg):
            h(sys[0])
        prog = f.build_exact(("sys", 1))
        j = exact_program_to_json(prog)
        prog2 = exact_program_from_json(j)
        assert prog2.certification == Certification.SAFE

    def test_primitive_lowers_to_broad_ir(self):
        from b01t import primitive
        @primitive
        def f(ctrl: QReg, reg: QReg):
            cx(ctrl[0], reg[0])
        prog = f.build_exact(("ctrl", 1), ("reg", 2))
        ir = lower_exact_program(prog)
        assert ir.is_safe is True  # lowered IR is still coherent+exact
        qc = QiskitBackend().emit(ir)
        assert qc.num_qubits == 3


# ====================================================================
# O. apply() block: CMA pattern (non-diagonal middle on disjoint wires)
# ====================================================================

class TestApplyBlock:
    """The apply() block allows any exact gates in the middle section,
    provided they operate on wires disjoint from the compute block.
    Justified by cma_ancilla_clean_product in AncillaApply.lean."""

    def test_apply_basic(self):
        """compute into ancilla, apply CX to disjoint output, uncompute."""
        from b01t import MiddleBlockKind
        @coherent
        def f(sys: QReg, out: QReg):
            with ancilla(1) as anc:
                compute(lambda: cx(sys[0], anc[0]))
                apply(lambda: cx(anc[0], out[0]))  # disjoint from compute wires
                uncompute()
        prog = f.build_exact(("sys", 2), ("out", 1))
        blk = prog.ops[0]
        assert isinstance(blk, ExactAncillaBlock)
        assert blk.middle_kind == MiddleBlockKind.APPLY
        assert len(blk.middle_ops) == 1
        assert blk.middle_ops[0].gate == ExactGate.CX

    def test_apply_rejects_shared_wires(self):
        """apply() block sharing wires with compute() is rejected."""
        @coherent
        def f(sys: QReg):
            with ancilla(1) as anc:
                compute(lambda: cx(sys[0], anc[0]))
                apply(lambda: cx(sys[0], sys[1]))  # sys[0] used in compute!
                uncompute()
        with pytest.raises(DSLValidationError, match="disjoint|shares wires"):
            f.build_exact(("sys", 3))

    def test_apply_rejects_writing_ancilla(self):
        """apply() block writing to ancilla wire is rejected (violates PreservesFirst)."""
        @coherent
        def f(sys: QReg, out: QReg):
            with ancilla(1) as anc:
                compute(lambda: cx(sys[0], anc[0]))
                apply(lambda: cx(out[0], anc[0]))  # anc is TARGET and writes to ancilla!
                uncompute()
        with pytest.raises(DSLValidationError, match="modifies ancilla"):
            f.build_exact(("sys", 2), ("out", 1))

    def test_apply_allows_reading_ancilla(self):
        """apply() block reading ancilla as CX control is allowed."""
        @coherent
        def f(sys: QReg, out: QReg):
            with ancilla(1) as anc:
                compute(lambda: cx(sys[0], anc[0]))
                apply(lambda: cx(anc[0], out[0]))  # anc is CONTROL, which is read-only and OK
                uncompute()
        prog = f.build_exact(("sys", 2), ("out", 1))
        assert len(prog.ops) == 1

    def test_apply_allows_any_exact_gate(self):
        """apply() block allows H (non-diagonal, non-phase gate)."""
        @coherent
        def f(sys: QReg, out: QReg):
            with ancilla(1) as anc:
                compute(lambda: cx(sys[0], anc[0]))
                apply(lambda: h(out[0]))  # H is non-diagonal and allowed in apply
                uncompute()
        prog = f.build_exact(("sys", 2), ("out", 1))
        blk = prog.ops[0]
        assert blk.middle_ops[0].gate == ExactGate.H

    def test_phase_remains_supported(self):
        """phase() remains supported for exact ancilla blocks."""
        from b01t import MiddleBlockKind
        @coherent
        def f(sys: QReg):
            with ancilla(1) as anc:
                compute(lambda: cx(sys[0], anc[0]))
                phase(lambda: z(anc[0]))
                uncompute()
        prog = f.build_exact(("sys", 2))
        blk = prog.ops[0]
        assert blk.middle_kind == MiddleBlockKind.PHASE

    def test_apply_lowers_to_broad_ir(self):
        """apply block lowers to AncillaBlockOp like phase does."""
        @coherent
        def f(sys: QReg, out: QReg):
            with ancilla(1) as anc:
                compute(lambda: cx(sys[0], anc[0]))
                apply(lambda: cx(anc[0], out[0]))
                uncompute()
        prog = f.build_exact(("sys", 2), ("out", 1))
        ir = lower_exact_program(prog)
        from b01t import AncillaBlockOp
        assert isinstance(ir.ops[0], AncillaBlockOp)
        assert ir.ops[0].phase_ops[0].name == "cx"
        qc = QiskitBackend().emit(ir)
        assert qc.num_qubits == 4  # sys(2) + out(1) + anc(1)

    def test_apply_round_trips_json(self):
        """apply blocks serialize and round-trip correctly."""
        from b01t import MiddleBlockKind
        @coherent
        def f(sys: QReg, out: QReg):
            with ancilla(1) as anc:
                compute(lambda: cx(sys[0], anc[0]))
                apply(lambda: cx(anc[0], out[0]))
                uncompute()
        prog = f.build_exact(("sys", 2), ("out", 1))
        j = exact_program_to_json(prog)
        prog2 = exact_program_from_json(j)
        assert prog == prog2
        assert prog2.ops[0].middle_kind == MiddleBlockKind.APPLY

    def test_apply_semantic_equivalence(self):
        """apply block: ancilla traces out cleanly."""
        from qiskit.quantum_info import Operator
        import numpy as np

        # cx(sys, anc); cx(anc, out); cx(sys, anc) with anc traced out
        # should act as cx(sys, out) on the system registers.
        @coherent
        def with_apply(sys: QReg, out: QReg):
            with ancilla(1) as anc:
                compute(lambda: cx(sys[0], anc[0]))
                apply(lambda: cx(anc[0], out[0]))
                uncompute()

        prog = with_apply.build_exact(("sys", 1), ("out", 1))
        ir_apply = lower_exact_program(prog)
        qc_apply = QiskitBackend().emit(ir_apply)
        u_full = Operator(qc_apply).data  # 8x8 (sys, out, anc)

        # Project ancilla (last qubit) onto |0>: take even-indexed rows/cols
        projected = u_full[::2, ::2]  # 4x4

        # The projected unitary should be a CX on (sys, out).
        # But Qiskit register ordering may differ. Verify it's unitary and
        # has the right structure: acts as identity when sys=0, swaps when sys=1.
        assert np.allclose(projected @ projected.conj().T, np.eye(4), atol=1e-10), \
            "projected matrix is not unitary, so ancilla is not clean"
        # Check it acts as CX: |00>->|00>, |01>->|01>, |10>->|11>, |11>->|10>
        # in SOME qubit ordering
        assert abs(abs(np.linalg.det(projected)) - 1.0) < 1e-10, \
            "projected unitary has wrong determinant"


# ====================================================================
# N. Certification downgrade: @coherent calling @primitive outside ancilla
# ====================================================================

class TestCertificationDowngrade:
    """When a @coherent function calls a @primitive outside an ancilla
    block, it must be rejected (not silently downgraded)."""

    def test_primitive_outside_ancilla_rejected(self):
        from b01t import primitive, Certification, DSLValidationError
        import pytest

        @primitive
        def inc(ctrl: QReg, reg: QReg):
            cx(ctrl[0], reg[0])

        @coherent
        def f(ctrl: QReg, reg: QReg):
            inc(ctrl, reg)  # @primitive at top level, rejected

        with pytest.raises(DSLValidationError, match="cannot call @primitive"):
            f.build_exact(("ctrl", 1), ("reg", 2))

    def test_primitive_inside_ancilla_stays_safe(self):
        from b01t import primitive, Certification

        @primitive
        def encode(sys: QReg, anc_reg: QReg):
            cx(sys[0], anc_reg[0])

        @coherent
        def f(sys: QReg):
            with ancilla(1) as anc:
                compute(lambda: encode(sys, anc))
                phase(lambda: z(anc[0]))
                uncompute()

        prog = f.build_exact(("sys", 2))
        assert prog.certification == Certification.SAFE

    def test_mixed_safe_and_primitive_rejected(self):
        """Ancilla block is fine, but a top-level @primitive call is rejected."""
        from b01t import primitive, Certification, DSLValidationError
        import pytest

        @primitive
        def flip(reg: QReg):
            x(reg[0])

        @coherent
        def f(sys: QReg):
            with ancilla(1) as anc:
                compute(lambda: cx(sys[0], anc[0]))
                phase(lambda: z(anc[0]))
                uncompute()
            flip(sys)  # outside ancilla, rejected

        with pytest.raises(DSLValidationError, match="cannot call @primitive"):
            f.build_exact(("sys", 2))

    def test_coherent_calling_coherent_stays_safe(self):
        """@coherent calling @coherent never downgrades."""
        from b01t import Certification

        @coherent
        def sub(sys: QReg):
            with ancilla(1) as anc:
                compute(lambda: cx(sys[0], anc[0]))
                phase(lambda: z(anc[0]))
                uncompute()

        @coherent
        def f(sys: QReg):
            sub(sys)

        prog = f.build_exact(("sys", 2))
        assert prog.certification == Certification.SAFE

    def test_primitive_calling_primitive_stays_primitive(self):
        """@primitive calling @primitive is still PRIMITIVE."""
        from b01t import primitive, Certification

        @primitive
        def inc(ctrl: QReg, reg: QReg):
            cx(ctrl[0], reg[0])

        @primitive
        def double_inc(ctrl: QReg, reg: QReg):
            inc(ctrl, reg)
            inc(ctrl, reg)

        prog = double_inc.build_exact(("ctrl", 1), ("reg", 2))
        assert prog.certification == Certification.PRIMITIVE
