"""Tests for all 9 manifest verification properties.

Run with: uv run python -m pytest tests/test_manifest.py -v
"""
import pytest
from b01t import (
    DSLValidationError, Effect, GateOp, IRProgram, QReg, QiskitBackend, Wire,
    adaptive, adjoint, ancilla, ccx, ccz, parametric, compute, cx, cz,
    dump_ir, h, is_safe_program, mcx, mcz, measure, measure_all,
    par, phase, repeat, ry, rz, s, sdg, swap, t, tdg, uncompute, x, z,
)
from b01t.core.gates import _ALLOWED_COMPUTE, _ALLOWED_PHASE, _inverse_gate


# ── Property 1: Gate classification is exact ──────────────────────────

class TestGateClassification:
    def test_compute_gates_accepted(self):
        for gate_fn, args in [(x, 1), (cx, 2), (ccx, 3), (mcx, 3), (swap, 2)]:
            @parametric
            def f(sys: QReg):
                with ancilla(1) as anc:
                    if gate_fn is mcx:
                        compute(lambda: mcx(sys.wires()[:2], anc[0]))
                    elif gate_fn is swap:
                        compute(lambda: swap(sys[0], anc[0]))
                    elif gate_fn is ccx:
                        compute(lambda: ccx(sys[0], sys[1], anc[0]))
                    elif gate_fn is cx:
                        compute(lambda: cx(sys[0], anc[0]))
                    else:
                        compute(lambda: x(anc[0]))
                    phase(lambda: z(anc[0]))
                    uncompute()
            f.build(("sys", 3))  # should not raise

    def test_phase_gates_accepted(self):
        @parametric
        def f(sys: QReg):
            with ancilla(1) as anc:
                compute(lambda: x(anc[0]))
                phase(lambda: (z(anc[0]), rz(0.5, anc[0]), s(anc[0]), t(anc[0])))
                uncompute()
        f.build(("sys", 2))

    def test_ry_rejected_in_compute(self):
        @parametric
        def f(sys: QReg):
            with ancilla(1) as anc:
                compute(lambda: ry(0.5, anc[0]))
                phase(lambda: z(anc[0]))
                uncompute()
        with pytest.raises(DSLValidationError, match="not allowed in compute"):
            f.build(("sys", 2))

    def test_ry_rejected_in_phase(self):
        @parametric
        def f(sys: QReg):
            with ancilla(1) as anc:
                compute(lambda: x(anc[0]))
                phase(lambda: ry(0.5, anc[0]))
                uncompute()
        with pytest.raises(DSLValidationError, match="not allowed in phase"):
            f.build(("sys", 2))

    def test_h_rejected_in_compute(self):
        @parametric
        def f(sys: QReg):
            with ancilla(1) as anc:
                compute(lambda: h(anc[0]))
                phase(lambda: z(anc[0]))
                uncompute()
        with pytest.raises(DSLValidationError, match="not allowed in compute"):
            f.build(("sys", 2))

    def test_h_rejected_in_phase(self):
        @parametric
        def f(sys: QReg):
            with ancilla(1) as anc:
                compute(lambda: x(anc[0]))
                phase(lambda: h(anc[0]))
                uncompute()
        with pytest.raises(DSLValidationError, match="not allowed in phase"):
            f.build(("sys", 2))

    def test_compute_gate_rejected_in_phase(self):
        @parametric
        def f(sys: QReg):
            with ancilla(1) as anc:
                compute(lambda: x(anc[0]))
                phase(lambda: cx(sys[0], anc[0]))
                uncompute()
        with pytest.raises(DSLValidationError, match="not allowed in phase"):
            f.build(("sys", 2))

    def test_phase_gate_rejected_in_compute(self):
        @parametric
        def f(sys: QReg):
            with ancilla(1) as anc:
                compute(lambda: rz(0.5, anc[0]))
                phase(lambda: z(anc[0]))
                uncompute()
        with pytest.raises(DSLValidationError, match="not allowed in compute"):
            f.build(("sys", 2))


# ── Property 2: Ancilla block structure is enforced ───────────────────

class TestAncillaStructure:
    def test_multiple_compute_rejected(self):
        """Second compute in same cycle (before uncompute) is rejected."""
        @parametric
        def f(sys: QReg):
            with ancilla(1) as anc:
                compute(lambda: x(anc[0]))
                phase(lambda: z(anc[0]))
                compute(lambda: x(anc[0]))  # no uncompute yet
                uncompute()
        with pytest.raises(DSLValidationError):
            f.build(("sys", 2))

    def test_multiple_phase_rejected(self):
        @parametric
        def f(sys: QReg):
            with ancilla(1) as anc:
                compute(lambda: x(anc[0]))
                phase(lambda: z(anc[0]))
                phase(lambda: z(anc[0]))
                uncompute()
        with pytest.raises(DSLValidationError, match="only one phase"):
            f.build(("sys", 2))

    def test_phase_before_compute_rejected(self):
        @parametric
        def f(sys: QReg):
            with ancilla(1) as anc:
                phase(lambda: z(anc[0]))
                compute(lambda: x(anc[0]))
                uncompute()
        with pytest.raises(DSLValidationError, match="must follow compute"):
            f.build(("sys", 2))

    def test_uncompute_before_phase_rejected(self):
        @parametric
        def f(sys: QReg):
            with ancilla(1) as anc:
                compute(lambda: x(anc[0]))
                uncompute()
        with pytest.raises(DSLValidationError, match="must follow phase"):
            f.build(("sys", 2))

    def test_missing_uncompute_rejected(self):
        @parametric
        def f(sys: QReg):
            with ancilla(1) as anc:
                compute(lambda: x(anc[0]))
                phase(lambda: z(anc[0]))
                # no uncompute
        with pytest.raises(DSLValidationError, match="incomplete"):
            f.build(("sys", 2))

    def test_measure_inside_ancilla_rejected(self):
        @adaptive
        def f(sys: QReg):
            with ancilla(1) as anc:
                compute(lambda: measure(anc[0]))
                phase(lambda: z(anc[0]))
                uncompute()
        with pytest.raises(DSLValidationError):
            f.build(("sys", 2))

    def test_multi_stage_accepted(self):
        """AncBlock.seq: two compute/phase/uncompute cycles on same ancilla."""
        @parametric
        def f(sys: QReg):
            with ancilla(1) as anc:
                compute(lambda: cx(sys[0], anc[0]))
                phase(lambda: z(anc[0]))
                uncompute()
                compute(lambda: cx(sys[1], anc[0]))
                phase(lambda: z(anc[0]))
                uncompute()
        ir = f.build(("sys", 3))
        assert ir.is_safe
        assert len(ir.ops) == 2  # two AncillaBlockOps


# ── Property 3: Uncompute is the exact inverse ───────────────────────

class TestUncompute:
    def test_self_inverse_uncompute(self):
        @parametric
        def f(sys: QReg):
            with ancilla(1) as anc:
                compute(lambda: (cx(sys[0], anc[0]), ccx(sys[0], sys[1], anc[0]), x(anc[0])))
                phase(lambda: z(anc[0]))
                uncompute()
        ir = f.build(("sys", 3))
        blk = ir.ops[0]
        # Reversed: [x, ccx, cx], and all are self-inverse.
        assert len(blk.uncompute_ops) == 3
        assert blk.uncompute_ops[0].name == "x"
        assert blk.uncompute_ops[1].name == "ccx"
        assert blk.uncompute_ops[2].name == "cx"

    def test_rz_rejected_in_compute(self):
        @parametric
        def f(sys: QReg):
            with ancilla(1) as anc:
                compute(lambda: rz(0.5, anc[0]))
                phase(lambda: z(anc[0]))
                uncompute()
        with pytest.raises(DSLValidationError, match="not allowed in compute"):
            f.build(("sys", 2))


# ── Property 4: SWAP rejection ───────────────────────────────────────

class TestSwapRejection:
    def test_dirty_swap_pattern_rejected(self):
        @parametric
        def f(sys: QReg):
            with ancilla(1) as anc:
                compute(lambda: (cx(sys[0], anc[0]), cx(anc[0], sys[0]), cx(sys[0], anc[0])))
                phase(lambda: z(anc[0]))
                uncompute()
        with pytest.raises(DSLValidationError, match="dirty-swap"):
            f.build(("sys", 2))

    def test_non_swap_cx_pattern_accepted(self):
        @parametric
        def f(sys: QReg):
            with ancilla(1) as anc:
                compute(lambda: (cx(sys[0], anc[0]), cx(sys[1], anc[0])))
                phase(lambda: z(anc[0]))
                uncompute()
        f.build(("sys", 3))  # should not raise


# ── Property 5: Adjoint respects restrictions ─────────────────────────

class TestAdjoint:
    def test_adjoint_inside_ancilla_rejected(self):
        @parametric
        def sub(s: QReg):
            h(s[0])

        @parametric
        def f(sys: QReg):
            with ancilla(1) as anc:
                adjoint(sub, sys)
        with pytest.raises(DSLValidationError, match="cannot be used inside"):
            f.build(("sys", 2))

    def test_adjoint_routes_through_append_op(self):
        """Adjoint output goes through _append_op, so gate checks apply."""
        @parametric
        def sub(s: QReg):
            h(s[0])

        @parametric
        def f(sys: QReg):
            adjoint(sub, sys)  # outside ancilla: should work
        ir = f.build(("sys", 2))
        assert ir.is_safe
        assert ir.ops[0].name == "h"  # H is self-inverse

    def test_adjoint_of_ancilla_block_is_safe(self):
        @parametric
        def sub(sys: QReg):
            with ancilla(1) as anc:
                compute(lambda: cx(sys[0], anc[0]))
                phase(lambda: z(anc[0]))
                uncompute()

        @parametric
        def f(sys: QReg):
            adjoint(sub, sys)
        ir = f.build(("sys", 2))
        assert ir.is_safe

    def test_adjoint_of_par_is_safe(self):
        @parametric
        def sub(a: QReg, b: QReg):
            par(lambda: h(a[0]), lambda: x(b[0]))

        @parametric
        def f(a: QReg, b: QReg):
            adjoint(sub, a, b)
        ir = f.build(("a", 2), ("b", 2))
        assert ir.is_safe


# ── Property 6: Safety checker is structural ──────────────────────────

class TestSafetyChecker:
    def test_adaptive_not_safe(self):
        @adaptive
        def f(sys: QReg):
            h(sys[0])
            measure_all(sys)
        ir = f.build(("sys", 2))
        assert not ir.is_safe

    def test_coherent_with_valid_ancilla_safe(self):
        @parametric
        def f(sys: QReg):
            h(sys[0])
            with ancilla(1) as anc:
                compute(lambda: cx(sys[0], anc[0]))
                phase(lambda: z(anc[0]))
                uncompute()
        ir = f.build(("sys", 2))
        assert ir.is_safe

    def test_coherent_no_ancilla_safe(self):
        @parametric
        def f(sys: QReg):
            h(sys[0])
            x(sys[1])
        ir = f.build(("sys", 2))
        assert ir.is_safe

    def test_par_safe(self):
        @parametric
        def f(a: QReg, b: QReg):
            par(lambda: h(a[0]), lambda: x(b[0]))
        ir = f.build(("a", 1), ("b", 1))
        assert ir.is_safe

    def test_is_safe_program_direct(self):
        """Call is_safe_program directly with hand-crafted ops."""
        w = Wire("q", 0)
        good_ops = [GateOp("h", (w,), ())]
        assert is_safe_program(Effect.COHERENT, good_ops)
        assert not is_safe_program(Effect.ADAPTIVE, good_ops)


# ── Property 7: Denotational soundness (Qiskit compilation) ──────────

class TestDenotational:
    def test_ancilla_block_compiles(self):
        @parametric
        def f(sys: QReg):
            with ancilla(1) as anc:
                compute(lambda: cx(sys[0], anc[0]))
                phase(lambda: z(anc[0]))
                uncompute()
        ir = f.build(("sys", 2))
        qc = QiskitBackend().emit(ir)
        assert qc.num_qubits == 3  # 2 sys + 1 anc
        assert qc.size() == 3  # cx, z, cx

    def test_par_compiles(self):
        @parametric
        def f(a: QReg, b: QReg):
            par(lambda: h(a[0]), lambda: x(b[0]))
        ir = f.build(("a", 1), ("b", 1))
        qc = QiskitBackend().emit(ir)
        assert qc.num_qubits == 2
        assert qc.size() == 2

    def test_multi_stage_compiles(self):
        @parametric
        def f(sys: QReg):
            with ancilla(1) as anc:
                compute(lambda: cx(sys[0], anc[0]))
                phase(lambda: z(anc[0]))
                uncompute()
                compute(lambda: cx(sys[1], anc[0]))
                phase(lambda: z(anc[0]))
                uncompute()
        ir = f.build(("sys", 3))
        qc = QiskitBackend().emit(ir)
        assert qc.size() == 6  # 2 stages * 3 gates each


# ── Property 8: SWAP counterexample ──────────────────────────────────

class TestSwapCounterexample:
    def test_swap_in_compute_rejected(self):
        """The 3-CX swap pattern in compute blocks is rejected."""
        @parametric
        def f(sys: QReg):
            with ancilla(1) as anc:
                compute(lambda: (
                    cx(sys[0], anc[0]),
                    cx(anc[0], sys[0]),
                    cx(sys[0], anc[0]),
                ))
                phase(lambda: z(anc[0]))
                uncompute()
        with pytest.raises(DSLValidationError, match="dirty-swap"):
            f.build(("sys", 2))


# ── Property 9: Completeness witness ─────────────────────────────────

class TestCompleteness:
    def test_any_single_qubit_unitary_expressible(self):
        """Any 1-qubit unitary is expressible (builds without error).
        Parameterized rotations are not in the exact-safe fragment."""
        @parametric
        def arb_rotation(sys: QReg):
            rz(0.3, sys[0])
            ry(0.7, sys[0])
            rz(1.2, sys[0])
        ir = arb_rotation.build(("sys", 1))
        assert not ir.is_safe  # expressible but not exact-safe

    def test_cnot_is_safe(self):
        @parametric
        def cnot(sys: QReg):
            cx(sys[0], sys[1])
        ir = cnot.build(("sys", 2))
        assert ir.is_safe

    def test_system_only_multi_qubit(self):
        """Multi-qubit unitary from exact gates, no ancilla needed."""
        @parametric
        def two_qubit(sys: QReg):
            h(sys[0])
            cx(sys[0], sys[1])
            t(sys[1])
            cx(sys[0], sys[1])
            h(sys[0])
        ir = two_qubit.build(("sys", 2))
        assert ir.is_safe


# ── Effect system ────────────────────────────────────────────────────

class TestEffectSystem:
    def test_coherent_rejects_measure(self):
        @parametric
        def f(sys: QReg):
            measure(sys[0])
        with pytest.raises(DSLValidationError, match="cannot measure"):
            f.build(("sys", 2))

    def test_coherent_rejects_if_then(self):
        @parametric
        def f(sys: QReg):
            from b01t import if_then
            if_then("cond", lambda: x(sys[0]))
        with pytest.raises(DSLValidationError, match="cannot branch"):
            f.build(("sys", 2))

    def test_coherent_rejects_adaptive_call(self):
        @adaptive
        def sub(sys: QReg):
            measure_all(sys)

        @parametric
        def f(sys: QReg):
            sub(sys)
        with pytest.raises(DSLValidationError, match="cannot call adaptive"):
            f.build(("sys", 2))
