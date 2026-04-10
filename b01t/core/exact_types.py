"""Exact AST: closed gate set, ops, and ExactProgram."""
from __future__ import annotations

from dataclasses import dataclass
from enum import Enum
from typing import Union

from .types import QReg, Wire


# ---------------------------------------------------------------------------
# Closed gate enum: no parameterized rotations, no free-form strings
# ---------------------------------------------------------------------------

class ExactGate(Enum):
    """Exact gate set: synthesisable from {H, S, T, CNOT}."""
    # Single-qubit
    X = "X"
    H = "H"
    Z = "Z"
    S = "S"
    SDG = "SDG"
    T = "T"
    TDG = "TDG"
    # Two-qubit
    CX = "CX"
    CZ = "CZ"
    SWAP = "SWAP"
    # Three-qubit
    CCX = "CCX"
    CCZ = "CCZ"
    # Multi-controlled
    MCX = "MCX"
    MCZ = "MCZ"


# Gate classification for ancilla blocks
EXACT_COMPUTE_GATES = frozenset({
    ExactGate.X, ExactGate.CX, ExactGate.CCX, ExactGate.SWAP, ExactGate.MCX,
})

EXACT_PHASE_GATES = frozenset({
    ExactGate.Z, ExactGate.CZ, ExactGate.CCZ,
    ExactGate.S, ExactGate.SDG, ExactGate.T, ExactGate.TDG,
    ExactGate.MCZ,
})


# ---------------------------------------------------------------------------
# Exact op types
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class ExactGateOp:
    gate: ExactGate
    wires: tuple[Wire, ...]


class MiddleBlockKind(Enum):
    """The middle section of an ancilla block: phase (diagonal) or apply (disjoint)."""
    PHASE = "phase"
    APPLY = "apply"


@dataclass(frozen=True)
class ExactAncillaBlock:
    """Ancilla-disciplined block: compute / middle / uncompute.

    The middle section is either:
    - PHASE (CPU pattern): diagonal gates only (Z, CZ, S, T, etc.)
    - APPLY (CMA pattern): any exact gates, but must operate on wires
      disjoint from the compute block's wires (PreservesFirst condition).
    """
    ancilla: QReg
    compute_ops: tuple[ExactGateOp, ...]
    middle_ops: tuple[ExactGateOp, ...]
    uncompute_ops: tuple[ExactGateOp, ...]
    middle_kind: MiddleBlockKind = MiddleBlockKind.PHASE


@dataclass(frozen=True)
class ExactParOp:
    left_ops: tuple[ExactOp, ...]
    right_ops: tuple[ExactOp, ...]


ExactOp = Union[ExactGateOp, ExactAncillaBlock, ExactParOp]


# ---------------------------------------------------------------------------
# Certification level: IsSafe vs IsCoh from the Lean proof
# ---------------------------------------------------------------------------

class Certification(Enum):
    """Proof-aligned certification level for exact programs.

    SAFE (IsSafe): all scratch is ancilla-managed via compute/phase/uncompute.
                   Structurally certified ancilla-clean. Hero theorem applies.
    PRIMITIVE (IsCoh): exact gates, coherent/unitary, but scratch registers are
                       caller-managed. The DSL trusts but does not certify
                       ancilla cleanliness.
    """
    SAFE = "safe"
    PRIMITIVE = "primitive"


# ---------------------------------------------------------------------------
# Exact program: no is_safe boolean, certification by construction
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class ExactProgram:
    """An exact coherent program built from the closed gate set.

    ``certification`` records whether the program is fully ancilla-certified
    (``SAFE``, from ``@coherent``) or uses caller-managed scratch
    (``PRIMITIVE``, from ``@primitive``).
    """
    name: str
    regs: tuple[QReg, ...]
    ops: tuple[ExactOp, ...]
    certification: Certification = Certification.SAFE
