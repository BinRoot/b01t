"""Classical SIR epidemic rollout: exact value (any H), branch sampler, simulator.

Cell states are encoded as (inf, rem) bit pairs:
    S = (0, 0)   I = (1, 0)   R = (0, 1) or (1, 1)

The exact computation is a forward DP over per-cell (inf, rem) tuples,
mixing uniform-random vaccination with per-cell independent SIR events.
"""
from __future__ import annotations

from collections import defaultdict
from dataclasses import dataclass
from random import Random
from typing import DefaultDict, Dict, List, Tuple

from .epidemic_spec import EpidemicSpec

CellState = Tuple[int, int]   # (inf, rem)
GridState = Tuple[CellState, ...]


@dataclass(frozen=True)
class EpidemicSample:
    selectors: Tuple[int, ...]
    dice: Tuple[Tuple[int, ...], ...]


def _initial_state(spec: EpidemicSpec) -> GridState:
    n = spec.n_cells
    grid = [(0, 0)] * n
    for i in spec.initial_infected:
        grid[i] = (1, 0)
    return tuple(grid)


def _per_cell_event_distribution(
    spec: EpidemicSpec,
    state: GridState,
) -> List[Dict[CellState, float]]:
    """For each cell, the distribution over its next (inf, rem) given the current grid."""
    n = spec.n_cells
    nbrs = spec.neighbors()
    out: List[Dict[CellState, float]] = []
    for cell in range(n):
        inf, rem = state[cell]
        if rem == 1:
            out.append({(inf, 1): 1.0})
        elif inf == 1:
            p_rec = spec.gamma_num / spec.gamma_den
            out.append({(0, 1): p_rec, (1, 0): 1.0 - p_rec})
        else:
            k = sum(1 for nb in nbrs[cell] if state[nb][0] == 1)
            p_inf = min(k * spec.beta_num / spec.beta_den, 1.0)
            out.append({(1, 0): p_inf, (0, 0): 1.0 - p_inf})
    return out


def _apply_vaccination(state: GridState, target: int) -> GridState:
    inf, rem = state[target]
    if inf == 1 or rem == 1:
        return state  # no-op on already-infected/recovered
    grid = list(state)
    grid[target] = (0, 1)
    return tuple(grid)


def _round_distribution(
    spec: EpidemicSpec,
    state: GridState,
    round_idx: int,
) -> Dict[GridState, float]:
    """Distribution over next-round grids under the harness sampler.

    The selector is uniform over [0, choices), where choices is
    n_susceptible_initially in round 0 and n_cells thereafter (matching
    `random_epidemic_sample`). Values ≥ #susceptible route to the sentinel
    no-op. This is the per-branch distribution the harness verifies; the
    quantum oracle prepares the wider 2^w superposition, but on every
    in-range value its behavior agrees branch-by-branch with this rollout.
    """
    n = spec.n_cells
    susceptible = [i for i in range(n) if state[i] == (0, 0)]
    out: DefaultDict[GridState, float] = defaultdict(float)

    choices = spec.n_susceptible_initially if round_idx == 0 else n

    candidate_states: List[Tuple[GridState, float]] = []
    if not susceptible:
        candidate_states.append((state, 1.0))
    else:
        per_index = 1.0 / choices
        for target in susceptible:
            candidate_states.append((_apply_vaccination(state, target), per_index))
        sentinel_mass = (choices - len(susceptible)) / choices
        if sentinel_mass > 0:
            candidate_states.append((state, sentinel_mass))

    for vaxed, base_p in candidate_states:
        cell_dists = _per_cell_event_distribution(spec, vaxed)
        running: Dict[Tuple[CellState, ...], float] = {(): 1.0}
        for cd in cell_dists:
            nxt: DefaultDict[Tuple[CellState, ...], float] = defaultdict(float)
            for prefix, p_prefix in running.items():
                for cell_state, p_cell in cd.items():
                    nxt[prefix + (cell_state,)] += p_prefix * p_cell
            running = dict(nxt)
        for full, p_full in running.items():
            out[full] += base_p * p_full

    return dict(out)


def classical_epidemic_payoff_exact(spec: EpidemicSpec) -> float:
    """Exact P[final infected count <= threshold] under uniform vaccination, any H."""
    dist: Dict[GridState, float] = {_initial_state(spec): 1.0}
    for round_idx in range(spec.horizon):
        nxt: DefaultDict[GridState, float] = defaultdict(float)
        for state, p in dist.items():
            for next_state, q in _round_distribution(spec, state, round_idx).items():
                nxt[next_state] += p * q
        dist = dict(nxt)

    payoff = 0.0
    for state, p in dist.items():
        infected = sum(1 for cell in state if cell[0] == 1)
        if infected <= spec.threshold:
            payoff += p
    return payoff


def random_epidemic_sample(spec: EpidemicSpec, rng: Random) -> EpidemicSample:
    sels: List[int] = []
    dice: List[Tuple[int, ...]] = []
    for h in range(spec.horizon):
        choices = spec.n_susceptible_initially if h == 0 else spec.n_cells
        sels.append(rng.randrange(max(1, choices)))
        dice.append(tuple(rng.randrange(spec.die_sides) for _ in range(spec.n_cells)))
    return EpidemicSample(tuple(sels), tuple(dice))


def direct_epidemic_rollout(
    spec: EpidemicSpec,
    sample: EpidemicSample,
) -> Tuple[Tuple[int, ...], Tuple[int, ...], int]:
    """Classical rollout on one branch. Returns (final inf, final rem, payoff)."""
    n = spec.n_cells
    nbrs = spec.neighbors()
    inf = [0] * n
    rem = [0] * n
    for i in spec.initial_infected:
        inf[i] = 1

    for h in range(spec.horizon):
        susceptible = [i for i in range(n) if inf[i] == 0 and rem[i] == 0]
        sel = sample.selectors[h]
        if susceptible and sel < len(susceptible):
            rem[susceptible[sel]] = 1

        inf_new, rem_new = list(inf), list(rem)
        for cell in range(n):
            die = sample.dice[h][cell]
            if inf[cell] == 0 and rem[cell] == 0:
                k = sum(1 for nb in nbrs[cell] if inf[nb] == 1)
                if die < spec.infection_threshold(k):
                    inf_new[cell] = 1
            elif inf[cell] == 1 and rem[cell] == 0:
                if die < spec.recovery_threshold():
                    inf_new[cell] = 0
                    rem_new[cell] = 1
        inf, rem = inf_new, rem_new

    payoff = 1 if sum(inf) <= spec.threshold else 0
    return tuple(inf), tuple(rem), payoff
