"""TDD tests for issues identified in review.md.

Organized into three sections:
  1. STARTER (red): Crisp failures tied to concrete implementation bugs.
     All of these MUST fail before we start fixing code.
  2. REGRESSION (green): Guards that already pass. They stay green as
     we fix the starter tests; if any turn red, we broke something.
  3. DEFERRED: Policy-heavy or ambitious tests parked for phase 2.

Run with: uv run python -m pytest tests/test_review_issues.py -v
"""
import pytest
from b01t import (
    DSLValidationError, Effect, GateOp, IRProgram, QReg, QiskitBackend, Wire,
    adaptive, adjoint, ancilla, ccx, ccz, parametric, compute, cx, cry, cz,
    dump_ir, h, is_safe_program, mcx, mcz, measure, measure_all,
    par, phase, repeat, rx, ry, rz, s, sdg, swap, t, tdg, uncompute, x, z,
)
from b01t.core.gates import _ALLOWED_COMPUTE, _ALLOWED_PHASE, _inverse_gate
from b01t.core.types import ParOp
from b01t.kit.control import if_then


# ====================================================================
# SECTION 1: STARTER (all red, all undeniable bugs)
# ====================================================================

class TestStarterWireValidation:
    """Gate emission checks only isinstance(Wire), not aliasing or membership."""

    def test_duplicate_wires_rejected_cx(self):
        """cx(q, q) is physically meaningless because control == target."""
        @parametric
        def f(sys: QReg):
            cx(sys[0], sys[0])
        with pytest.raises(DSLValidationError, match="distinct|duplicate|same"):
            f.build(("sys", 2))

    def test_wire_from_undeclared_register(self):
        """Using a Wire from a register not in the program."""
        @parametric
        def f(sys: QReg):
            foreign = Wire("ghost", 0)
            h(foreign)
        with pytest.raises(DSLValidationError, match="register|undeclared|unknown"):
            f.build(("sys", 2))


class TestStarterParDisjointness:
    """par() claims disjoint composition but never checks."""

    def test_same_wire_in_both_branches_rejected(self):
        """Both branches operate on sys[0], so they are not disjoint."""
        @parametric
        def f(sys: QReg):
            par(lambda: h(sys[0]), lambda: x(sys[0]))
        with pytest.raises(DSLValidationError, match="disjoint|overlap"):
            f.build(("sys", 2))


class TestStarterMeasurementCollision:
    """Backend keys classical register by quantum register name with size 1,
    so repeated measure() calls on the same register collide."""

    def test_two_measures_same_register_distinct_bits(self):
        """measure(sys[0]) then measure(sys[1]) should use distinct classical bits."""
        @adaptive
        def f(sys: QReg):
            h(sys[0])
            h(sys[1])
            measure(sys[0])
            measure(sys[1])
        ir = f.build(("sys", 3))
        qc = QiskitBackend().emit(ir)
        assert qc.num_clbits >= 2


class TestStarterExactSafety:
    """is_safe_program accepts any GateOp, which is too broad for the exact fragment."""

    def test_rejects_arbitrary_ry(self):
        """ry(0.5) is not in the exact gate set."""
        w = Wire("q", 0)
        ops = [GateOp("ry", (w,), (0.5,))]
        assert not is_safe_program(Effect.COHERENT, ops)

    def test_rejects_unknown_gate(self):
        """A bogus gate name should not be considered safe."""
        w = Wire("q", 0)
        ops = [GateOp("unicorn_gate", (w,), ())]
        assert not is_safe_program(Effect.COHERENT, ops)


# ====================================================================
# SECTION 2: REGRESSION (already green, must stay green)
# ====================================================================

class TestRegressionWireValidation:
    def test_non_wire_argument_caught(self):
        """Passing an int instead of a Wire is already caught."""
        @parametric
        def f(sys: QReg):
            h(0)  # type: ignore
        with pytest.raises(DSLValidationError, match="Wire"):
            f.build(("sys", 2))

    def test_wire_index_out_of_range(self):
        """QReg.__getitem__ raises IndexError for out-of-range."""
        @parametric
        def f(sys: QReg):
            h(sys[5])
        with pytest.raises((DSLValidationError, IndexError)):
            f.build(("sys", 2))


class TestRegressionParDisjointness:
    def test_different_wires_same_register_passes(self):
        """Different wires within the same register are wire-disjoint."""
        @parametric
        def f(sys: QReg):
            par(lambda: h(sys[0]), lambda: x(sys[1]))
        ir = f.build(("sys", 3))
        assert ir.is_safe

    def test_truly_disjoint_passes(self):
        """Branches on separate registers are fine."""
        @parametric
        def f(a: QReg, b: QReg):
            par(lambda: h(a[0]), lambda: x(b[0]))
        ir = f.build(("a", 1), ("b", 1))
        assert ir.is_safe


class TestRegressionMeasurement:
    def test_measure_labels_unique(self):
        """Each measure() returns a distinct label."""
        @adaptive
        def f(sys: QReg):
            m0 = measure(sys[0])
            m1 = measure(sys[1])
            assert m0 != m1
        f.build(("sys", 3))

    def test_measure_after_measure_all_no_collision(self):
        """measure_all + measure on different register works."""
        @adaptive
        def f(a: QReg, b: QReg):
            measure_all(a)
            measure(b[0])
        ir = f.build(("a", 2), ("b", 1))
        qc = QiskitBackend().emit(ir)
        assert qc.num_clbits == 3


class TestRegressionExactSafety:
    def test_exact_gates_still_safe(self):
        """Named exact gates remain safe."""
        @parametric
        def f(sys: QReg):
            h(sys[0])
            x(sys[1])
            cx(sys[0], sys[1])
            t(sys[0])
            s(sys[1])
        ir = f.build(("sys", 2))
        assert ir.is_safe

    def test_sdg_tdg_still_safe(self):
        @parametric
        def f(sys: QReg):
            sdg(sys[0])
            tdg(sys[0])
        ir = f.build(("sys", 1))
        assert ir.is_safe

    def test_ccx_ccz_still_safe(self):
        @parametric
        def f(sys: QReg):
            ccx(sys[0], sys[1], sys[2])
            ccz(sys[0], sys[1], sys[2])
        ir = f.build(("sys", 3))
        assert ir.is_safe

    def test_swap_still_safe(self):
        @parametric
        def f(sys: QReg):
            swap(sys[0], sys[1])
        ir = f.build(("sys", 2))
        assert ir.is_safe

    def test_mcx_mcz_still_safe(self):
        @parametric
        def f(sys: QReg):
            mcx(sys.wires()[:2], sys[2])
            mcz(sys.wires()[:2], sys[2])
        ir = f.build(("sys", 3))
        assert ir.is_safe

    def test_is_safe_accepts_exact_gate_at_toplevel(self):
        w = Wire("q", 0)
        ops = [GateOp("h", (w,), ())]
        assert is_safe_program(Effect.COHERENT, ops)


# ====================================================================
# SECTION 3: DEFERRED (phase 2, once core invariants are in place)
# ====================================================================

class TestDeferredAdaptiveCompilation:
    """if_then lowering requires IR-level classical-bit mapping first."""

    @pytest.mark.skip(reason="phase 2: backend does not lower IfOp yet")
    def test_if_then_compiles_to_qiskit(self):
        @adaptive
        def f(sys: QReg):
            h(sys[0])
            result = measure(sys[0])
            if_then(result, lambda: x(sys[1]))
        ir = f.build(("sys", 2))
        qc = QiskitBackend().emit(ir)
        assert qc.num_qubits == 2

    @pytest.mark.skip(reason="phase 2: backend does not lower IfOp yet")
    def test_if_then_else_compiles(self):
        @adaptive
        def f(sys: QReg):
            h(sys[0])
            result = measure(sys[0])
            if_then(result, lambda: x(sys[1]), lambda: z(sys[1]))
        ir = f.build(("sys", 2))
        qc = QiskitBackend().emit(ir)
        assert qc.num_qubits == 2


class TestDeferredAncillaCleanliness:
    """Policy-heavy: requires deciding whether compute must touch ancilla wires."""

    @pytest.mark.skip(reason="phase 2: policy decision on compute-must-touch-ancilla")
    def test_compute_without_ancilla_wire_rejected(self):
        @parametric
        def f(sys: QReg):
            with ancilla(1) as anc:
                compute(lambda: cx(sys[0], sys[1]))
                phase(lambda: z(anc[0]))
                uncompute()
        with pytest.raises(DSLValidationError, match="ancilla|must touch"):
            f.build(("sys", 3))

    @pytest.mark.skip(reason="phase 2: policy decision on bare system ops in compute")
    def test_bare_system_flip_in_compute_rejected(self):
        @parametric
        def f(sys: QReg):
            with ancilla(1) as anc:
                compute(lambda: x(sys[0]))
                phase(lambda: z(anc[0]))
                uncompute()
        with pytest.raises(DSLValidationError, match="ancilla|system"):
            f.build(("sys", 2))


class TestExactSafetyExtended:
    """Extended exact-safety boundary: parameterized rotations, wire aliasing, par overlap."""

    def test_rejects_arbitrary_rx(self):
        @parametric
        def f(sys: QReg):
            rx(0.3, sys[0])
        ir = f.build(("sys", 1))
        assert not ir.is_safe

    def test_rejects_arbitrary_rz(self):
        @parametric
        def f(sys: QReg):
            rz(0.7, sys[0])
        ir = f.build(("sys", 1))
        assert not ir.is_safe

    def test_rejects_arbitrary_cry(self):
        @parametric
        def f(sys: QReg):
            cry(1.0, sys[0], sys[1])
        ir = f.build(("sys", 2))
        assert not ir.is_safe

    def test_partial_overlap_rejected(self):
        @parametric
        def f(sys: QReg):
            par(
                lambda: (h(sys[0]), cx(sys[0], sys[1])),
                lambda: (h(sys[1]), x(sys[2])),
            )
        with pytest.raises(DSLValidationError, match="disjoint|overlap"):
            f.build(("sys", 4))

    def test_duplicate_wires_rejected_swap(self):
        @parametric
        def f(sys: QReg):
            swap(sys[0], sys[0])
        with pytest.raises(DSLValidationError, match="distinct|duplicate|same"):
            f.build(("sys", 2))

    def test_duplicate_wires_rejected_ccx(self):
        @parametric
        def f(sys: QReg):
            ccx(sys[0], sys[0], sys[1])
        with pytest.raises(DSLValidationError, match="distinct|duplicate|same"):
            f.build(("sys", 3))
