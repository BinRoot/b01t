"""Iterative Quantum Amplitude Estimation circuit.

Applies the Grover iterate Q = A S_0 A† O_chi at increasing depths
(Q^1, Q^2, Q^4, ...) and measures after each. Classical MLE on the
measurement outcomes estimates sin^2(theta) = Pr[good].

This avoids the controlled-Q problem of QPE-based QAE. The Grover
iterate Q is inlined as gate-level operations.

Each depth-k circuit is @adaptive (it measures).
"""

from typing import Callable

from b01t.core import QReg, adaptive, parametric, h, x, z, cz, mcx, measure_all
from b01t.kit import ancilla, compute, phase, uncompute, adjoint


def _inline_grover_step(sys: QReg, prep_fn, oracle_fn, prep_dslfn):
    """Emit one Grover iterate Q = oracle ; A† ; S_0 ; A.

    Inlined at gate level so it works inside @parametric/@adaptive.
    prep_fn/oracle_fn: raw Python callables.
    prep_dslfn: a DSLFunction wrapping prep_fn (needed for adjoint).
    """
    # O_chi: mark good states
    oracle_fn(sys)
    # A†: undo state prep
    adjoint(prep_dslfn, sys)
    # S_0: zero-state reflection (inlined to avoid @coherent call)
    n = len(sys)
    if n == 1:
        z(sys[0])
    elif n == 2:
        for w in sys:
            x(w)
        cz(sys[0], sys[1])
        for w in sys:
            x(w)
    else:
        for w in sys:
            x(w)
        with ancilla(1) as anc:
            compute(lambda: mcx(sys.wires()[:-1], anc[0]))
            phase(lambda: cz(anc[0], sys[-1]))
            uncompute()
        for w in sys:
            x(w)
    # A: re-apply state prep
    prep_fn(sys)


def make_qae_round(
    state_prep: Callable,
    oracle: Callable,
    depth: int,
):
    """Return an @adaptive circuit for one QAE round at the given depth.

    Applies A (state prep) then Q^depth, then measures.

    Args:
        state_prep: @coherent or @parametric function(sys) implementing A
        oracle:     @coherent or @parametric function(sys) implementing O_chi
        depth:      number of Grover iterations (0 = just measure A|0>)

    The returned function takes:
        sys: work register (starts at |0>)
    """
    # Extract the raw Python function from ExactDSLFunction wrappers
    prep_fn = getattr(state_prep, 'fn', state_prep)
    oracle_fn = getattr(oracle, 'fn', oracle)

    # Create a @parametric DSLFunction for adjoint() compatibility
    @parametric
    def _prep_broad(sys: QReg):
        prep_fn(sys)

    @adaptive
    def qae_round(sys: QReg):
        prep_fn(sys)
        for _ in range(depth):
            _inline_grover_step(sys, prep_fn, oracle_fn, _prep_broad)
        return measure_all(sys)

    return qae_round


def make_qae_schedule(
    state_prep: Callable,
    oracle: Callable,
    max_depth: int,
):
    """Return a list of @adaptive circuits for iterative QAE.

    Returns circuits for depths 0, 1, 2, 4, ..., 2^(max_depth-1).
    Run each circuit multiple times, collect measurement statistics,
    then feed into ml_estimate() from zoo.qae.estimation.

    Args:
        state_prep: @coherent or @parametric function(sys) implementing A
        oracle:     @coherent or @parametric function(sys) implementing O_chi
        max_depth:  number of depth levels
    """
    circuits = []
    for k in range(max_depth):
        depth = 1 << k if k > 0 else 0
        circuits.append(make_qae_round(state_prep, oracle, depth))
    return circuits
