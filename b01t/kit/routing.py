"""Context-aware routing: ancilla/compute/phase/uncompute/par/adjoint.

These functions detect whether they're inside an exact (@coherent) or
broad (@parametric/@adaptive) build context and route to the correct
implementation automatically. Users write one set of names.
"""

from typing import Any, Callable, Optional


def ancilla(size: int):
    """Create an ancilla block. Routes to exact or broad path by context."""
    from b01t.core.exact_builder import _exact_ctx, _ExactAncillaManager
    if _exact_ctx() is not None:
        return _ExactAncillaManager(size)
    from b01t.core.ancilla import _AncillaManager
    return _AncillaManager(size)


def compute(fn: Callable[[], Any]) -> None:
    """Compute section inside an ancilla block. Routes by context."""
    from b01t.core.exact_builder import _exact_ctx
    if _exact_ctx() is not None:
        from b01t.core.exact_builder import exact_compute
        return exact_compute(fn)
    from b01t.core.ancilla import compute as _broad_compute
    return _broad_compute(fn)


def phase(fn: Callable[[], Any]) -> None:
    """Phase section inside an ancilla block. Routes by context."""
    from b01t.core.exact_builder import _exact_ctx
    if _exact_ctx() is not None:
        from b01t.core.exact_builder import exact_phase
        return exact_phase(fn)
    from b01t.core.ancilla import phase as _broad_phase
    return _broad_phase(fn)


def apply(fn: Callable[[], Any]) -> None:
    """Apply section inside an ancilla block (CMA pattern). Routes by context.

    Allows any exact gates on wires disjoint from the compute block.
    In broad context, falls through to phase (broad IR doesn't distinguish).
    """
    from b01t.core.exact_builder import _exact_ctx
    if _exact_ctx() is not None:
        from b01t.core.exact_builder import exact_apply
        return exact_apply(fn)
    # Broad path: no separate apply, so treat it as phase.
    from b01t.core.ancilla import phase as _broad_phase
    return _broad_phase(fn)


def uncompute() -> None:
    """Uncompute section. Routes by context."""
    from b01t.core.exact_builder import _exact_ctx
    if _exact_ctx() is not None:
        from b01t.core.exact_builder import exact_uncompute
        return exact_uncompute()
    from b01t.core.ancilla import uncompute as _broad_uncompute
    return _broad_uncompute()


def par(fn1: Callable[[], Any], fn2: Callable[[], Any]) -> None:
    """Parallel composition. Routes by context."""
    from b01t.core.exact_builder import _exact_ctx
    if _exact_ctx() is not None:
        from b01t.core.exact_builder import exact_par
        return exact_par(fn1, fn2)
    from .control import par as _broad_par
    return _broad_par(fn1, fn2)


def adjoint(fn, *args) -> None:
    """Adjoint (inverse). Routes by context."""
    from b01t.core.exact_builder import _exact_ctx, ExactDSLFunction, exact_adjoint
    if _exact_ctx() is not None and isinstance(fn, ExactDSLFunction):
        return exact_adjoint(fn, *args)
    from b01t.core.builder import adjoint as _broad_adjoint
    return _broad_adjoint(fn, *args)
