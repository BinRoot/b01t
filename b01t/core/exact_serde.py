"""JSON and dict serialization for ExactProgram (format exact-oracle-v1)."""

import json
from typing import Any

from .types import DSLValidationError, QReg, Wire
from .exact_types import (
    ExactGate, ExactGateOp, ExactAncillaBlock, ExactParOp, ExactOp, ExactProgram,
    Certification, MiddleBlockKind,
)
from .exact_validate import validate_exact_ops


# ---------------------------------------------------------------------------
# Serialization: ExactProgram -> dict/JSON
# ---------------------------------------------------------------------------

def _wire_to_dict(w: Wire) -> dict[str, Any]:
    return {"reg": w.reg, "index": w.index, "kind": w.kind}


def _reg_to_dict(r: QReg) -> dict[str, Any]:
    return {"name": r.name, "size": r.size, "kind": r.kind}


def _gate_op_to_dict(op: ExactGateOp) -> dict[str, Any]:
    return {
        "op": "gate",
        "gate": op.gate.value,
        "wires": [_wire_to_dict(w) for w in op.wires],
    }


def _op_to_dict(op: ExactOp) -> dict[str, Any]:
    if isinstance(op, ExactGateOp):
        return _gate_op_to_dict(op)
    if isinstance(op, ExactAncillaBlock):
        return {
            "op": "ancilla",
            "ancilla": _reg_to_dict(op.ancilla),
            "compute": [_gate_op_to_dict(g) for g in op.compute_ops],
            "middle": [_gate_op_to_dict(g) for g in op.middle_ops],
            "middle_kind": op.middle_kind.value,
            "uncompute": [_gate_op_to_dict(g) for g in op.uncompute_ops],
        }
    if isinstance(op, ExactParOp):
        return {
            "op": "par",
            "left": [_op_to_dict(o) for o in op.left_ops],
            "right": [_op_to_dict(o) for o in op.right_ops],
        }
    raise DSLValidationError(f"unknown exact op type: {type(op).__name__}")


def exact_program_to_dict(prog: ExactProgram) -> dict[str, Any]:
    """Serialize an ``ExactProgram`` to a plain dict."""
    return {
        "certification": prog.certification.value,
        "format": "exact-oracle-v1",
        "name": prog.name,
        "ops": [_op_to_dict(op) for op in prog.ops],
        "regs": [_reg_to_dict(r) for r in prog.regs],
    }


def exact_program_to_json(prog: ExactProgram) -> str:
    """Serialize an ``ExactProgram`` to a deterministic JSON string."""
    return json.dumps(exact_program_to_dict(prog), sort_keys=True, indent=2)


# ---------------------------------------------------------------------------
# Deserialization: dict/JSON -> ExactProgram
# ---------------------------------------------------------------------------

def _wire_from_dict(d: dict[str, Any]) -> Wire:
    return Wire(reg=d["reg"], index=d["index"], kind=d.get("kind", "sys"))


def _reg_from_dict(d: dict[str, Any]) -> QReg:
    return QReg(name=d["name"], size=d["size"], kind=d.get("kind", "sys"))


def _gate_op_from_dict(d: dict[str, Any]) -> ExactGateOp:
    gate = ExactGate(d["gate"])
    wires = tuple(_wire_from_dict(w) for w in d["wires"])
    return ExactGateOp(gate=gate, wires=wires)


def _op_from_dict(d: dict[str, Any]) -> ExactOp:
    tag = d["op"]
    if tag == "gate":
        return _gate_op_from_dict(d)
    if tag == "ancilla":
        # Support both old "phase" key and new "middle" key
        middle_data = d.get("middle", d.get("phase", []))
        middle_kind = MiddleBlockKind(d.get("middle_kind", "phase"))
        return ExactAncillaBlock(
            ancilla=_reg_from_dict(d["ancilla"]),
            compute_ops=tuple(_gate_op_from_dict(g) for g in d["compute"]),
            middle_ops=tuple(_gate_op_from_dict(g) for g in middle_data),
            uncompute_ops=tuple(_gate_op_from_dict(g) for g in d["uncompute"]),
            middle_kind=middle_kind,
        )
    if tag == "par":
        return ExactParOp(
            left_ops=tuple(_op_from_dict(o) for o in d["left"]),
            right_ops=tuple(_op_from_dict(o) for o in d["right"]),
        )
    raise DSLValidationError(f"unknown op tag in JSON: '{tag}'")


def exact_program_from_dict(data: dict[str, Any]) -> ExactProgram:
    """Deserialize an ``ExactProgram`` from a plain dict.

    Validates format version and re-checks structural invariants.
    """
    fmt = data.get("format")
    if fmt != "exact-oracle-v1":
        raise DSLValidationError(
            f"unsupported exact oracle format: '{fmt}' (expected 'exact-oracle-v1')")
    regs = tuple(_reg_from_dict(r) for r in data["regs"])
    ops = tuple(_op_from_dict(o) for o in data["ops"])
    cert = Certification(data.get("certification", "safe"))
    validate_exact_ops(ops, regs)
    return ExactProgram(name=data["name"], regs=regs, ops=ops, certification=cert)


def exact_program_from_json(s: str) -> ExactProgram:
    """Deserialize an ``ExactProgram`` from a JSON string."""
    return exact_program_from_dict(json.loads(s))
