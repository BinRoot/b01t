"""IR pretty-printer."""

from typing import Sequence

from b01t.core.types import (
    Op, GateOp, MeasureOp, MeasureAllOp, IfOp, AncillaBlockOp, ParOp, IRProgram,
)


def _format_gate(op: GateOp) -> str:
    params = ""
    if op.params:
        params = f"({', '.join(repr(p) for p in op.params)})"
    return f"{op.name}{params} " + ", ".join(str(w) for w in op.wires)


def _dump_ops(lines: list[str], ops: Sequence[Op], indent: int = 0) -> None:
    pad = "  " * indent
    for op in ops:
        if isinstance(op, GateOp):
            lines.append(f"{pad}{_format_gate(op)}")
        elif isinstance(op, MeasureOp):
            lines.append(f"{pad}measure {op.wire}")
        elif isinstance(op, MeasureAllOp):
            lines.append(f"{pad}measure_all {op.reg}[0:{op.size}]")
        elif isinstance(op, IfOp):
            lines.append(f"{pad}if {op.cond!r}:")
            _dump_ops(lines, op.then_ops, indent + 1)
            if op.else_ops:
                lines.append(f"{pad}else:")
                _dump_ops(lines, op.else_ops, indent + 1)
        elif isinstance(op, AncillaBlockOp):
            lines.append(f"{pad}with ancilla({op.ancilla.size}) as {op.ancilla.name}:")
            if op.compute_ops:
                lines.append(f"{pad}  compute:")
                _dump_ops(lines, op.compute_ops, indent + 2)
            if op.phase_ops:
                lines.append(f"{pad}  phase:")
                _dump_ops(lines, op.phase_ops, indent + 2)
            if op.uncompute_ops:
                lines.append(f"{pad}  uncompute:")
                _dump_ops(lines, op.uncompute_ops, indent + 2)
        elif isinstance(op, ParOp):
            lines.append(f"{pad}par:")
            lines.append(f"{pad}  left:")
            _dump_ops(lines, op.left_ops, indent + 2)
            lines.append(f"{pad}  right:")
            _dump_ops(lines, op.right_ops, indent + 2)
        else:
            lines.append(f"{pad}{op!r}")


def dump_ir(ir: IRProgram) -> str:
    lines = [
        f"program {ir.name}",
        f"effect: {ir.effect.value}",
        f"safe: {ir.is_safe}",
        "registers:",
    ]
    for reg in ir.regs:
        lines.append(f"  - {reg.name}[{reg.size}] ({reg.kind})")
    lines.append("ops:")
    _dump_ops(lines, ir.ops, indent=1)
    return "\n".join(lines)
