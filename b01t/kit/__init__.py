"""Kit: routing, control, backend, IR, registry, CLI, arithmetic."""

# Context-routing combinators (auto-route exact vs broad)
from .routing import ancilla, compute, phase, apply, uncompute, par, adjoint

# Control flow (broad-path specific)
from .control import repeat, for_each, if_then

# IR printer
from .ir import dump_ir

# Backend
from .backend import QiskitBackend

# Registry
from .registry import PackageMeta, PackageRegistry, DEFAULT_REGISTRY

# Controlled-call utility
from .controlled import controlled_call, inline_exact

# Arithmetic subpackage
from . import arithmetic
