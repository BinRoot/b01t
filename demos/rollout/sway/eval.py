"""Verification harness for the coherent Sway rollout oracle.

Compiles the oracle with prepare_superpositions=False (a permutation on
basis states), seeds selector and dice qubits with a sampled classical
branch, runs the circuit as a classical reversible permutation, and
compares the resulting payoff/board against the direct classical rollout.
"""
from __future__ import annotations

from math import sqrt
from random import Random
from typing import Dict, List, Tuple

from qiskit import QuantumCircuit

from b01t import QiskitBackend, lower_exact_program
from b01t.kit.arithmetic import int_to_bits

from .classical import (
    Board,
    SwaySample,
    direct_rollout_from_sample,
    random_sample,
)
from .rollout_oracle import make_rollout_oracle
from .sway_spec import SwaySpec


def _build_permutation_oracle(spec: SwaySpec) -> Tuple[QuantumCircuit, Dict[str, Tuple[int, int]]]:
    """Compile prep-free oracle. Returns (qc, name → (start, width))."""
    oracle = make_rollout_oracle(spec, prepare_superpositions=False)
    prog = oracle.build_exact(*spec.register_specs())
    qc = QiskitBackend().emit(lower_exact_program(prog))
    layout: Dict[str, Tuple[int, int]] = {}
    offset = 0
    for r in qc.qregs:
        layout[r.name] = (offset, r.size)
        offset += r.size
    return qc, layout


def _write_value(bits: List[int], start: int, width: int, value: int) -> None:
    for i, b in enumerate(int_to_bits(value, width)):
        bits[start + i] = b


def initial_bits_from_sample(
    layout: Dict[str, Tuple[int, int]],
    spec: SwaySpec,
    sample: SwaySample,
    n_qubits: int,
) -> List[int]:
    """Embed a classical sample into the input qubits (LSB-first per register)."""
    bits = [0] * n_qubits
    die_w = spec.die_width
    n = spec.n_cells
    for r in range(1, spec.horizon + 1):
        for name, value in (
            (f"sel_b{r}", sample.black_selectors[r - 1]),
            (f"sel_w{r}", sample.white_selectors[r - 1]),
        ):
            start, width = layout[name]
            if width > 0:
                _write_value(bits, start, width, value)
        dice_start, _ = layout[f"dice_{r}"]
        for cell, die_value in enumerate(sample.dice[r - 1]):
            _write_value(bits, dice_start + cell * die_w, die_w, die_value)
    return bits


def emulate_basis_circuit(qc: QuantumCircuit, initial_bits: List[int]) -> List[int]:
    """Run a permutation circuit (X/CX/CCX/MCX) classically. Errors on H."""
    bits = list(initial_bits)
    qubit_index = {q: qc.find_bit(q).index for q in qc.qubits}
    for inst in qc.data:
        name = inst.operation.name
        qinds = [qubit_index[q] for q in inst.qubits]
        if name == "x":
            bits[qinds[0]] ^= 1
        elif name in {"cx", "ccx", "mcx"}:
            if all(bits[i] == 1 for i in qinds[:-1]):
                bits[qinds[-1]] ^= 1
        elif name == "barrier":
            continue
        else:
            raise ValueError(f"basis emulator saw non-classical gate {name!r}")
    return bits


def final_board_from_bits(
    layout: Dict[str, Tuple[int, int]],
    spec: SwaySpec,
    bits: List[int],
) -> Board:
    occ_start, occ_w = layout["occ"]
    occ = tuple(bits[occ_start + i] for i in range(occ_w))
    color_start, color_w = layout[f"color_{spec.horizon}"]
    color = tuple(bits[color_start + i] for i in range(color_w))
    return occ, color


def verify_sampled_branches(
    spec: SwaySpec,
    samples: int = 256,
    seed: int = 7,
) -> Tuple[int, int]:
    """Compare the prep-free oracle against the direct rollout on `samples` branches."""
    qc, layout = _build_permutation_oracle(spec)
    payoff_start, _ = layout["payoff"]
    rng = Random(seed)
    matches = 0
    for _ in range(samples):
        sample = random_sample(spec, rng)
        expected_board, expected_payoff = direct_rollout_from_sample(spec, sample)
        bits0 = initial_bits_from_sample(layout, spec, sample, qc.num_qubits)
        bits1 = emulate_basis_circuit(qc, bits0)
        got_board = final_board_from_bits(layout, spec, bits1)
        got_payoff = bits1[payoff_start]
        if got_board == expected_board and got_payoff == expected_payoff:
            matches += 1
    return matches, samples


def monte_carlo_payoff_from_oracle(
    spec: SwaySpec,
    samples: int = 1000,
    seed: int = 11,
) -> Tuple[float, float]:
    """MC estimate of the oracle's payoff probability. Returns (mean, SE)."""
    qc, layout = _build_permutation_oracle(spec)
    payoff_start, _ = layout["payoff"]
    rng = Random(seed)
    wins = 0
    for _ in range(samples):
        sample = random_sample(spec, rng)
        bits0 = initial_bits_from_sample(layout, spec, sample, qc.num_qubits)
        bits1 = emulate_basis_circuit(qc, bits0)
        wins += bits1[payoff_start]
    p = wins / samples
    se = sqrt(max(p * (1 - p), 1e-12) / samples)
    return p, se
