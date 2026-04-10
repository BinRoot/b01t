"""b01t package: core DSL, kit utilities, and algorithm zoo."""
# Import subpackages
from . import core, kit, zoo

# ---------------------------------------------------------------------------
# Re-export core names
# ---------------------------------------------------------------------------

# Types
from .core.types import (
    DSLValidationError,
    Effect,
    Wire,
    QReg,
    GateOp,
    MeasureOp,
    MeasureAllOp,
    IfOp,
    AncillaBlockOp,
    ParOp,
    Op,
    IRProgram,
)

# Gates (public API)
from .core.gates import (
    x, h, z, s, sdg, t, tdg,
    ry, rx, rz,
    cx, cz, swap, cry, crz,
    ccx, ccz,
    mcx, mcz,
    measure, measure_all,
)

# Decorators
from .core.exact_builder import coherent, primitive, ExactDSLFunction
from .core.builder import parametric, adaptive, DSLFunction

# Safety checker (broad IR)
from .core.safety import is_safe_program

# Exact core types
from .core.exact_types import (
    ExactGate,
    ExactGateOp,
    ExactAncillaBlock,
    ExactParOp,
    ExactOp,
    ExactProgram,
    Certification,
    MiddleBlockKind,
    EXACT_COMPUTE_GATES,
    EXACT_PHASE_GATES,
)

# Lowering and serialization
from .core.exact_lowering import lower_exact_program
from .core.exact_serde import (
    exact_program_to_dict,
    exact_program_from_dict,
    exact_program_to_json,
    exact_program_from_json,
)

# ---------------------------------------------------------------------------
# Re-export kit names
# ---------------------------------------------------------------------------

# Context-routing combinators (auto-route exact vs broad)
from .kit.routing import ancilla, compute, phase, apply, uncompute, par, adjoint

# Control flow (broad-path specific)
from .kit.control import repeat, for_each, if_then

# IR printer
from .kit.ir import dump_ir

# Backend
from .kit.backend import QiskitBackend

# Registry
from .kit.registry import PackageMeta, PackageRegistry, DEFAULT_REGISTRY

__all__ = [
    # Decorators
    "coherent",
    "primitive",
    "parametric",
    "adaptive",
    "Certification",
    # Context-routing combinators
    "ancilla",
    "compute",
    "phase",
    "apply",
    "uncompute",
    "par",
    "adjoint",
    # Gates
    "x", "h", "z", "s", "sdg", "t", "tdg",
    "ry", "rx", "rz",
    "cx", "cz", "swap", "cry", "crz",
    "ccx", "ccz",
    "mcx", "mcz",
    "measure", "measure_all",
    # Types
    "DSLValidationError", "Effect", "Wire", "QReg",
    "GateOp", "MeasureOp", "MeasureAllOp", "IfOp",
    "AncillaBlockOp", "ParOp", "Op", "IRProgram",
    # Exact core
    "ExactGate", "ExactGateOp", "ExactAncillaBlock",
    "ExactParOp", "ExactOp", "ExactProgram",
    "ExactDSLFunction",
    "EXACT_COMPUTE_GATES", "EXACT_PHASE_GATES",
    # Lowering and serde
    "lower_exact_program",
    "exact_program_to_dict", "exact_program_from_dict",
    "exact_program_to_json", "exact_program_from_json",
    # Infra
    "DSLFunction", "QiskitBackend",
    "PackageMeta", "PackageRegistry", "DEFAULT_REGISTRY",
    "is_safe_program", "dump_ir",
    "repeat", "for_each", "if_then",
    "MiddleBlockKind",
]
