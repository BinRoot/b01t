"""Core: IR types, gates, builders, validation, and exact program support."""

# Types and IR
from .types import (
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

# Exact core types
from .exact_types import (
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

# Gates (public API; private allowlists live in gates.py)
from .gates import (
    x, h, z, s, sdg, t, tdg,
    ry, rx, rz,
    cx, cz, swap, cry, crz,
    ccx, ccz,
    mcx, mcz,
    measure, measure_all,
)

# Decorators
from .exact_builder import coherent, primitive, ExactDSLFunction
from .builder import parametric, adaptive, DSLFunction

# Safety checker (broad IR)
from .safety import is_safe_program

# Lowering and serialization
from .exact_lowering import lower_exact_program
from .exact_serde import (
    exact_program_to_dict,
    exact_program_from_dict,
    exact_program_to_json,
    exact_program_from_json,
)
