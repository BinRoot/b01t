"""Core types: Wire, QReg, Op variants, IRProgram, Effect."""

from dataclasses import dataclass, field
from enum import Enum
from typing import Any, Optional


class DSLValidationError(RuntimeError):
    pass


class Effect(Enum):
    COHERENT = "coherent"
    ADAPTIVE = "adaptive"


@dataclass(frozen=True)
class Wire:
    reg: str
    index: int
    kind: str = "sys"

    def __repr__(self) -> str:
        return f"{self.reg}[{self.index}]"


class QReg:
    def __init__(self, name: str, size: int, kind: str = "sys"):
        self.name = name
        self.size = size
        self.kind = kind
        self._wires = [Wire(name, i, kind=kind) for i in range(size)]

    def __getitem__(self, idx: int) -> Wire:
        return self._wires[idx]

    def wires(self) -> list[Wire]:
        return list(self._wires)

    def __iter__(self):
        return iter(self._wires)

    def __len__(self) -> int:
        return self.size

    def __repr__(self) -> str:
        return f"QReg(name={self.name!r}, size={self.size}, kind={self.kind!r})"

    def __eq__(self, other: object) -> bool:
        if not isinstance(other, QReg):
            return NotImplemented
        return self.name == other.name and self.size == other.size and self.kind == other.kind

    def __hash__(self) -> int:
        return hash((self.name, self.size, self.kind))


# ---------------------------------------------------------------------------
# IR op types
# ---------------------------------------------------------------------------

@dataclass
class GateOp:
    name: str
    wires: tuple[Wire, ...]
    params: tuple[Any, ...] = ()


@dataclass
class MeasureOp:
    wire: Wire


@dataclass
class MeasureAllOp:
    reg: str
    size: int


@dataclass
class IfOp:
    cond: Any
    then_ops: list[Any]
    else_ops: list[Any]


@dataclass
class AncillaBlockOp:
    ancilla: QReg
    compute_ops: list[GateOp]
    phase_ops: list[GateOp]
    uncompute_ops: list[GateOp]


@dataclass
class ParOp:
    """Parallel (tensor) composition of two sub-programs on disjoint registers."""
    left_ops: list  # list[Op]
    right_ops: list  # list[Op]


Op = GateOp | MeasureOp | MeasureAllOp | IfOp | AncillaBlockOp | ParOp


@dataclass
class IRProgram:
    name: str
    effect: Effect
    regs: list[QReg]
    ops: list[Op]
    is_safe: bool
