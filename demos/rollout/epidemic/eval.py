"""Verification harness for the coherent epidemic rollout oracle.

Mirrors the sway eval module: compiles the oracle with prep disabled,
seeds selector and dice qubits with a sampled branch, runs the circuit
classically, and compares to the direct rollout.
"""
from __future__ import annotations

from math import sqrt
from random import Random
from typing import Dict, List, Tuple

from qiskit import QuantumCircuit

from b01t import QiskitBackend, lower_exact_program
from b01t.kit.arithmetic import int_to_bits

from .classical import (
    EpidemicSample,
    direct_epidemic_rollout,
    random_epidemic_sample,
)
from .epidemic_spec import EpidemicSpec
from .rollout_oracle import make_epidemic_rollout_oracle


def _build_permutation_oracle(spec: EpidemicSpec) -> Tuple[QuantumCircuit, Dict[str, Tuple[int, int]]]:
    oracle = make_epidemic_rollout_oracle(spec, prepare_superpositions=False)
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
    spec: EpidemicSpec,
    sample: EpidemicSample,
    n_qubits: int,
) -> List[int]:
    bits = [0] * n_qubits
    die_w = spec.die_width
    for h in range(1, spec.horizon + 1):
        sel_name = f"sel_{h}"
        if sel_name in layout:
            start, width = layout[sel_name]
            if width > 0:
                _write_value(bits, start, width, sample.selectors[h - 1])
        dice_start, _ = layout[f"dice_{h}"]
        for cell, die_value in enumerate(sample.dice[h - 1]):
            _write_value(bits, dice_start + cell * die_w, die_w, die_value)
    return bits


def emulate_basis_circuit(qc: QuantumCircuit, initial_bits: List[int]) -> List[int]:
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


def final_state_from_bits(
    layout: Dict[str, Tuple[int, int]],
    spec: EpidemicSpec,
    bits: List[int],
) -> Tuple[Tuple[int, ...], Tuple[int, ...]]:
    inf_start, inf_w = layout[f"inf_{spec.horizon}"]
    rem_start, rem_w = layout[f"rem_{spec.horizon}"]
    inf = tuple(bits[inf_start + i] for i in range(inf_w))
    rem = tuple(bits[rem_start + i] for i in range(rem_w))
    return inf, rem


def verify_sampled_branches(
    spec: EpidemicSpec,
    samples: int = 256,
    seed: int = 7,
) -> Tuple[int, int]:
    qc, layout = _build_permutation_oracle(spec)
    payoff_start, _ = layout["payoff"]
    rng = Random(seed)
    matches = 0
    for _ in range(samples):
        sample = random_epidemic_sample(spec, rng)
        expected_inf, expected_rem, expected_payoff = direct_epidemic_rollout(spec, sample)
        bits0 = initial_bits_from_sample(layout, spec, sample, qc.num_qubits)
        bits1 = emulate_basis_circuit(qc, bits0)
        got_inf, got_rem = final_state_from_bits(layout, spec, bits1)
        got_payoff = bits1[payoff_start]
        if (got_inf, got_rem, got_payoff) == (expected_inf, expected_rem, expected_payoff):
            matches += 1
    return matches, samples


def monte_carlo_payoff_from_oracle(
    spec: EpidemicSpec,
    samples: int = 1000,
    seed: int = 11,
) -> Tuple[float, float]:
    qc, layout = _build_permutation_oracle(spec)
    payoff_start, _ = layout["payoff"]
    rng = Random(seed)
    wins = 0
    for _ in range(samples):
        sample = random_epidemic_sample(spec, rng)
        bits0 = initial_bits_from_sample(layout, spec, sample, qc.num_qubits)
        bits1 = emulate_basis_circuit(qc, bits0)
        wins += bits1[payoff_start]
    p = wins / samples
    se = sqrt(max(p * (1 - p), 1e-12) / samples)
    return p, se
