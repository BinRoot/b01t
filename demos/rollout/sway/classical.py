"""Classical Sway rollout: exact value, branch sampler, direct simulator.

The exact win-probability function and the per-branch direct simulator
serve as the ground truth for verifying the coherent oracle.
"""
from __future__ import annotations

from collections import defaultdict
from dataclasses import dataclass
from itertools import product
from random import Random
from typing import DefaultDict, Dict, List, Sequence, Tuple

from .sway_spec import SwaySpec

Board = Tuple[Tuple[int, ...], Tuple[int, ...]]
DICE_RANGE = 20  # flip probability is (4-k)/20 for k friendly neighbors


@dataclass(frozen=True)
class SwaySample:
    """One classical branch: per-round selectors and per-cell dice rolls."""
    black_selectors: Tuple[int, ...]
    white_selectors: Tuple[int, ...]
    dice: Tuple[Tuple[int, ...], ...]


def empty_board(spec: SwaySpec) -> Board:
    n = spec.n_cells
    return tuple([0] * n), tuple([0] * n)


def apply_move(board: Board, cell: int, player: int) -> Board:
    occ, color = board
    if occ[cell] != 0:
        raise ValueError("illegal move on occupied cell")
    new_occ = list(occ); new_occ[cell] = 1
    new_color = list(color); new_color[cell] = player
    return tuple(new_occ), tuple(new_color)


def count_friendly_neighbors(board: Board, cell: int, neighbors: Sequence[Sequence[int]]) -> int:
    occ, color = board
    if occ[cell] == 0:
        return 0
    return sum(1 for nb in neighbors[cell] if occ[nb] and color[nb] == color[cell])


def apply_flip_pattern(board: Board, flips: Sequence[int]) -> Board:
    occ, color = board
    new_color = list(color)
    for i, flip in enumerate(flips):
        if occ[i] and flip:
            new_color[i] ^= 1
    return occ, tuple(new_color)


def sway_distribution(board: Board, neighbors: Sequence[Sequence[int]]) -> Dict[Board, float]:
    occ, _ = board
    occupied = [i for i, bit in enumerate(occ) if bit]
    out: DefaultDict[Board, float] = defaultdict(float)
    for bits in product([0, 1], repeat=len(occupied)):
        full = [0] * len(occ)
        prob = 1.0
        for bit, cell in zip(bits, occupied):
            k = count_friendly_neighbors(board, cell, neighbors)
            p = (4 - k) / DICE_RANGE
            prob *= p if bit else (1.0 - p)
            full[cell] = bit
        out[apply_flip_pattern(board, full)] += prob
    return dict(out)


def rollout_distribution(spec: SwaySpec) -> Dict[Board, float]:
    neighbors = spec.neighbors()
    dist: Dict[Board, float] = {empty_board(spec): 1.0}
    for _ in range(spec.horizon):
        after_black: DefaultDict[Board, float] = defaultdict(float)
        for board, p in dist.items():
            empties = [i for i, bit in enumerate(board[0]) if bit == 0]
            for cell in empties:
                after_black[apply_move(board, cell, 1)] += p / len(empties)
        after_white: DefaultDict[Board, float] = defaultdict(float)
        for board, p in after_black.items():
            empties = [i for i, bit in enumerate(board[0]) if bit == 0]
            for cell in empties:
                after_white[apply_move(board, cell, 0)] += p / len(empties)
        after_sway: DefaultDict[Board, float] = defaultdict(float)
        for board, p in after_white.items():
            for nxt, q in sway_distribution(board, neighbors).items():
                after_sway[nxt] += p * q
        dist = dict(after_sway)
    return dist


def classical_black_win_probability(spec: SwaySpec) -> float:
    """Exact P[black wins] under uniform-random rollout, by full enumeration."""
    out = 0.0
    for board, p in rollout_distribution(spec).items():
        occ, color = board
        black = sum(1 for i in range(spec.n_cells) if occ[i] and color[i] == 1)
        white = sum(1 for i in range(spec.n_cells) if occ[i] and color[i] == 0)
        if black > white:
            out += p
    return out


def random_sample(spec: SwaySpec, rng: Random) -> SwaySample:
    """Draw one classical branch: selectors uniform over valid action counts."""
    n = spec.n_cells
    black_selectors: List[int] = []
    white_selectors: List[int] = []
    dice: List[Tuple[int, ...]] = []
    for round_idx in range(spec.horizon):
        # round 1: n empties for black, n-1 for white; round 2: n-2 / n-3; etc.
        black_selectors.append(rng.randrange(n - 2 * round_idx))
        white_selectors.append(rng.randrange(n - 2 * round_idx - 1))
        dice.append(tuple(rng.randrange(DICE_RANGE) for _ in range(n)))
    return SwaySample(tuple(black_selectors), tuple(white_selectors), tuple(dice))


def direct_rollout_from_sample(spec: SwaySpec, sample: SwaySample) -> Tuple[Board, int]:
    """Classical rollout on one branch: returns (final_board, payoff)."""
    neighbors = spec.neighbors()
    n = spec.n_cells
    board = empty_board(spec)
    for round_idx in range(spec.horizon):
        empties = [i for i, bit in enumerate(board[0]) if bit == 0]
        board = apply_move(board, empties[sample.black_selectors[round_idx]], 1)

        empties = [i for i, bit in enumerate(board[0]) if bit == 0]
        board = apply_move(board, empties[sample.white_selectors[round_idx]], 0)

        occ, color = board
        new_color = list(color)
        for cell in range(n):
            if occ[cell]:
                k = count_friendly_neighbors(board, cell, neighbors)
                if sample.dice[round_idx][cell] < (4 - k):
                    new_color[cell] ^= 1
        board = (occ, tuple(new_color))

    black = sum(1 for i in range(n) if board[0][i] and board[1][i] == 1)
    white = sum(1 for i in range(n) if board[0][i] and board[1][i] == 0)
    payoff = 1 if black > white else 0
    return board, payoff
