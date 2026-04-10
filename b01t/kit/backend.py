"""Qiskit backend: compile IR to QuantumCircuit."""

from typing import Sequence

from b01t.core.types import (
    DSLValidationError, Wire, IRProgram, Op,
    GateOp, AncillaBlockOp, ParOp, MeasureOp, MeasureAllOp, IfOp,
)


class QiskitBackend:
    def emit(self, ir: IRProgram):
        try:
            from qiskit import ClassicalRegister, QuantumCircuit, QuantumRegister
        except ImportError as exc:
            raise DSLValidationError(
                "Qiskit is required for backend emission. Install with 'pip install qiskit'."
            ) from exc

        qregs: dict[str, QuantumRegister] = {}
        cregs: dict[str, ClassicalRegister] = {}

        qreg_list = []
        for reg in ir.regs:
            qreg = QuantumRegister(reg.size, reg.name)
            qregs[reg.name] = qreg
            qreg_list.append(qreg)
        circuit = QuantumCircuit(*qreg_list, name=ir.name)

        def q(w: Wire):
            return qregs[w.reg][w.index]

        def emit_ops(ops: Sequence[Op]) -> None:
            for op in ops:
                if isinstance(op, GateOp):
                    name = op.name
                    if name == "x":
                        circuit.x(q(op.wires[0]))
                    elif name == "h":
                        circuit.h(q(op.wires[0]))
                    elif name == "z":
                        circuit.z(q(op.wires[0]))
                    elif name == "s":
                        circuit.s(q(op.wires[0]))
                    elif name == "sdg":
                        circuit.sdg(q(op.wires[0]))
                    elif name == "t":
                        circuit.t(q(op.wires[0]))
                    elif name == "tdg":
                        circuit.tdg(q(op.wires[0]))
                    elif name == "ry":
                        circuit.ry(op.params[0], q(op.wires[0]))
                    elif name == "rx":
                        circuit.rx(op.params[0], q(op.wires[0]))
                    elif name == "rz":
                        circuit.rz(op.params[0], q(op.wires[0]))
                    elif name == "cx":
                        circuit.cx(q(op.wires[0]), q(op.wires[1]))
                    elif name == "cz":
                        circuit.cz(q(op.wires[0]), q(op.wires[1]))
                    elif name == "swap":
                        circuit.swap(q(op.wires[0]), q(op.wires[1]))
                    elif name == "cry":
                        circuit.cry(op.params[0], q(op.wires[0]), q(op.wires[1]))
                    elif name == "crz":
                        circuit.crz(op.params[0], q(op.wires[0]), q(op.wires[1]))
                    elif name == "ccx":
                        circuit.ccx(q(op.wires[0]), q(op.wires[1]), q(op.wires[2]))
                    elif name == "ccz":
                        if hasattr(circuit, "ccz"):
                            circuit.ccz(q(op.wires[0]), q(op.wires[1]), q(op.wires[2]))
                        else:
                            circuit.h(q(op.wires[2]))
                            circuit.ccx(q(op.wires[0]), q(op.wires[1]), q(op.wires[2]))
                            circuit.h(q(op.wires[2]))
                    elif name == "mcx":
                        ctrls = [q(w) for w in op.wires[:-1]]
                        tgt = q(op.wires[-1])
                        circuit.mcx(ctrls, tgt)
                    elif name == "mcz":
                        ctrls = [q(w) for w in op.wires[:-1]]
                        tgt = q(op.wires[-1])
                        circuit.h(tgt)
                        circuit.mcx(ctrls, tgt)
                        circuit.h(tgt)
                    else:
                        raise DSLValidationError(f"backend does not support gate '{name}'")
                elif isinstance(op, AncillaBlockOp):
                    emit_ops(op.compute_ops)
                    emit_ops(op.phase_ops)
                    emit_ops(op.uncompute_ops)
                elif isinstance(op, ParOp):
                    emit_ops(op.left_ops)
                    emit_ops(op.right_ops)
                elif isinstance(op, MeasureOp):
                    cname = f"c_{op.wire.reg}_{op.wire.index}"
                    if cname not in cregs:
                        cregs[cname] = ClassicalRegister(1, cname)
                        circuit.add_register(cregs[cname])
                    circuit.measure(q(op.wire), cregs[cname][0])
                elif isinstance(op, MeasureAllOp):
                    cname = f"c_{op.reg}"
                    if cname not in cregs:
                        cregs[cname] = ClassicalRegister(op.size, cname)
                        circuit.add_register(cregs[cname])
                    for idx in range(op.size):
                        circuit.measure(qregs[op.reg][idx], cregs[cname][idx])
                elif isinstance(op, IfOp):
                    raise DSLValidationError("backend does not lower classical if-then in the MVP")
                else:
                    raise DSLValidationError(f"unknown op type: {type(op).__name__}")

        emit_ops(ir.ops)
        return circuit
