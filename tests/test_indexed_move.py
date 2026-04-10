"""Test the @coherent rank_select pattern (paper eq. 1).

Verifies that rank_select_scan inside compute/apply/uncompute
produces a structurally certified @coherent ExactProgram.
"""
import pytest
from b01t import (
    DSLValidationError, QReg, Wire, QiskitBackend,
    coherent, primitive, ancilla, compute, apply, uncompute,
    cx, x,
    ExactProgram, ExactAncillaBlock, Certification, MiddleBlockKind,
    lower_exact_program,
)
from b01t.zoo.rank_select import rank_select_scan


def rank_select_scan_4(occ_w, sel_w, mv_w, pre_w, eq_w):
    """rank_select_scan for n=4 cells."""
    rank_select_scan(occ_w, sel_w, mv_w, pre_w, eq_w, 4)


class TestRankSelect:
    """Tests for the paper's rank-select interface (eq. 1)."""

    def test_coherent_rank_select_builds(self):
        """rank_select with compute/apply/uncompute builds as @coherent SAFE."""
        n, w = 4, 3
        @coherent
        def rs(occ: QReg, sel: QReg, target: QReg):
            with ancilla(n + w + w) as scratch:
                mv = scratch.wires()[:n]
                pre = scratch.wires()[n:n+w]
                eq = scratch.wires()[n+w:]
                compute(lambda: rank_select_scan_4(occ.wires(), sel.wires(), mv, pre, eq))
                apply(lambda: [cx(mv[c], target[c]) for c in range(n)])
                uncompute()
        prog = rs.build_exact(("occ", 4), ("sel", 3), ("target", 4))
        assert isinstance(prog, ExactProgram)
        assert prog.certification == Certification.SAFE

    def test_apply_block_kind(self):
        """The ancilla block uses APPLY middle kind."""
        n, w = 4, 3
        @coherent
        def rs(occ: QReg, sel: QReg, target: QReg):
            with ancilla(n + w + w) as scratch:
                mv = scratch.wires()[:n]
                pre = scratch.wires()[n:n+w]
                eq = scratch.wires()[n+w:]
                compute(lambda: rank_select_scan_4(occ.wires(), sel.wires(), mv, pre, eq))
                apply(lambda: [cx(mv[c], target[c]) for c in range(n)])
                uncompute()
        prog = rs.build_exact(("occ", 4), ("sel", 3), ("target", 4))
        blk = prog.ops[0]
        assert isinstance(blk, ExactAncillaBlock)
        assert blk.middle_kind == MiddleBlockKind.APPLY

    def test_compiles_to_qiskit(self):
        """Lowered program compiles through backend."""
        n, w = 4, 3
        @coherent
        def rs(occ: QReg, sel: QReg, target: QReg):
            with ancilla(n + w + w) as scratch:
                mv = scratch.wires()[:n]
                pre = scratch.wires()[n:n+w]
                eq = scratch.wires()[n+w:]
                compute(lambda: rank_select_scan_4(occ.wires(), sel.wires(), mv, pre, eq))
                apply(lambda: [cx(mv[c], target[c]) for c in range(n)])
                uncompute()
        prog = rs.build_exact(("occ", 4), ("sel", 3), ("target", 4))
        ir = lower_exact_program(prog)
        qc = QiskitBackend().emit(ir)
        assert qc.num_qubits == 21  # occ(4)+sel(3)+target(4)+scratch(10)

    def test_scan_standalone_is_primitive(self):
        """The internal scan as @primitive has PRIMITIVE certification."""
        @primitive
        def scan(occ: QReg, sel: QReg, move: QReg, pre: QReg, eq: QReg):
            rank_select_scan_4(occ.wires(), sel.wires(), move.wires(), pre.wires(), eq.wires())
        prog = scan.build_exact(("occ", 4), ("sel", 3), ("move", 4), ("pre", 3), ("eq", 3))
        assert prog.certification == Certification.PRIMITIVE
