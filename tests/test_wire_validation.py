"""Tests for broad-path wire validation: out-of-range and undeclared wires."""
import pytest

from b01t import (
    QReg, Wire, DSLValidationError,
    parametric, adaptive, x, cx, measure, measure_all,
)


class TestGateWireValidation:
    def test_out_of_range_index_rejected(self):
        @parametric
        def f(sys: QReg):
            x(Wire("sys", 99))  # sys has 3 qubits, index 99 is invalid

        with pytest.raises(DSLValidationError, match="out of range"):
            f.build(("sys", 3))

    def test_undeclared_register_rejected(self):
        @parametric
        def f(sys: QReg):
            x(Wire("ghost", 0))  # "ghost" is not a declared register

        with pytest.raises(DSLValidationError, match="undeclared register"):
            f.build(("sys", 3))

    def test_valid_wire_accepted(self):
        @parametric
        def f(sys: QReg):
            x(sys[0])
            x(sys[2])

        ir = f.build(("sys", 3))
        assert len(ir.ops) == 2

    def test_boundary_index_accepted(self):
        @parametric
        def f(sys: QReg):
            x(sys[2])  # last valid index for size=3

        ir = f.build(("sys", 3))
        assert len(ir.ops) == 1


class TestMeasureWireValidation:
    def test_measure_undeclared_register_rejected(self):
        @adaptive
        def f(sys: QReg):
            measure(Wire("ghost", 0))

        with pytest.raises(DSLValidationError, match="undeclared register"):
            f.build(("sys", 3))

    def test_measure_out_of_range_rejected(self):
        @adaptive
        def f(sys: QReg):
            measure(Wire("sys", 99))

        with pytest.raises(DSLValidationError, match="out of range"):
            f.build(("sys", 3))

    def test_measure_valid_wire_accepted(self):
        @adaptive
        def f(sys: QReg):
            measure(sys[0])

        ir = f.build(("sys", 3))
        assert len(ir.ops) == 1

    def test_measure_all_undeclared_rejected(self):
        @adaptive
        def f(sys: QReg):
            measure_all(QReg(name="ghost", size=3))

        with pytest.raises(DSLValidationError, match="undeclared register"):
            f.build(("sys", 3))

    def test_measure_all_valid_accepted(self):
        @adaptive
        def f(sys: QReg):
            measure_all(sys)

        ir = f.build(("sys", 3))
        assert len(ir.ops) == 1
