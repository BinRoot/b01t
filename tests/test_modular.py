"""Tests for modular arithmetic zoo module."""
from b01t import (
    QReg,
    QiskitBackend,
    Certification,
    coherent,
    primitive,
    lower_exact_program,
)
from b01t.zoo.modular import (
    ctrl_modular_add_wires,
    modular_add_constant_wires,
    make_inplace_modular_mul,
    make_controlled_modular_exp,
)


class TestModularAdd:
    """Wire-level modular addition builds and compiles."""

    def test_uncontrolled_is_safe(self):
        @coherent
        def test_mod_add(b: QReg, scratch: QReg):
            n = len(b)
            const_w = scratch.wires()[:n]
            cin = scratch[n]
            flag = scratch[n + 1]
            modular_add_constant_wires(
                b.wires(), 3, 7, const_w, cin, flag)

        prog = test_mod_add.build_exact(("b", 3), ("scratch", 5))
        assert prog.certification == Certification.SAFE

    def test_controlled_is_safe(self):
        @coherent
        def test_ctrl_add(ctrl: QReg, b: QReg, scratch: QReg):
            n = len(b)
            const_w = scratch.wires()[:n]
            cin = scratch[n]
            flag = scratch[n + 1]
            ctrl_modular_add_wires(
                ctrl[0], b.wires(), 3, 7, const_w, cin, flag)

        prog = test_ctrl_add.build_exact(
            ("ctrl", 1), ("b", 3), ("scratch", 5))
        assert prog.certification == Certification.SAFE

    def test_compiles_to_qiskit(self):
        @coherent
        def test_mod_add(b: QReg, scratch: QReg):
            n = len(b)
            const_w = scratch.wires()[:n]
            cin = scratch[n]
            flag = scratch[n + 1]
            modular_add_constant_wires(
                b.wires(), 5, 7, const_w, cin, flag)

        prog = test_mod_add.build_exact(("b", 3), ("scratch", 5))
        ir = lower_exact_program(prog)
        qc = QiskitBackend().emit(ir)
        assert qc.num_qubits == 8


class TestInplaceModularMul:
    """@primitive in-place modular multiplication."""

    def test_builds(self):
        mul_fn = make_inplace_modular_mul(2, 7)
        prog = mul_fn.build_exact(("y", 3), ("acc", 3), ("scratch", 5))
        # Primitive certification (SWAP prevents SAFE)
        assert prog.certification == Certification.PRIMITIVE

    def test_compiles_to_qiskit(self):
        mul_fn = make_inplace_modular_mul(3, 7)
        prog = mul_fn.build_exact(("y", 3), ("acc", 3), ("scratch", 5))
        ir = lower_exact_program(prog)
        qc = QiskitBackend().emit(ir)
        assert qc.num_qubits == 11  # 3 + 3 + 5

    def test_different_modulus(self):
        mul_fn = make_inplace_modular_mul(7, 15)  # gcd(7,15)=1
        prog = mul_fn.build_exact(("y", 4), ("acc", 4), ("scratch", 6))
        assert prog.certification == Certification.PRIMITIVE


class TestControlledModularExp:
    """@primitive controlled modular exponentiation."""

    def test_builds(self):
        exp_fn = make_controlled_modular_exp(2, 7, num_ctrl_bits=3)
        prog = exp_fn.build_exact(
            ("ctrl", 3), ("y", 3), ("acc", 3), ("scratch", 6))
        assert prog.certification == Certification.PRIMITIVE

    def test_compiles_to_qiskit(self):
        exp_fn = make_controlled_modular_exp(2, 7, num_ctrl_bits=3)
        prog = exp_fn.build_exact(
            ("ctrl", 3), ("y", 3), ("acc", 3), ("scratch", 6))
        ir = lower_exact_program(prog)
        qc = QiskitBackend().emit(ir)
        assert qc.num_qubits == 15  # 3 + 3 + 3 + 6

    def test_single_ctrl_bit(self):
        exp_fn = make_controlled_modular_exp(3, 7, num_ctrl_bits=1)
        prog = exp_fn.build_exact(
            ("ctrl", 1), ("y", 3), ("acc", 3), ("scratch", 6))
        assert prog.certification == Certification.PRIMITIVE
