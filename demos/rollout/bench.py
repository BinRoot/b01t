"""Validation and scaling tables for the rollout oracle.

Compiles each instance, gathers Qiskit qubit/depth/gate counts, runs
the verification harness for the small instances, and prints
resource counts at the larger scales.

Run:
    uv run python -m demos.rollout.bench
    uv run python -m demos.rollout.bench --validate-only
    uv run python -m demos.rollout.bench --scale-only

Runtime (single 24-core x86_64, 2026-04):
    --scale-only     ≈ 30 s (compilation only)
    --validate-only  ≈ 10 min (256 sampled branches + 1000 MC samples
                     + classical exact-value DP per Table 1 row;
                     Sway 5x5 H=3 exact-value DP is the bottleneck)
"""
from __future__ import annotations

import argparse
import time
from dataclasses import dataclass
from typing import Optional, Tuple

from b01t import QiskitBackend, lower_exact_program

from demos.rollout.sway.sway_spec import SwaySpec
from demos.rollout.sway.rollout_oracle import make_rollout_oracle as make_sway_oracle
from demos.rollout.sway.eval import (
    verify_sampled_branches as verify_sway_branches,
    monte_carlo_payoff_from_oracle as mc_sway_payoff,
)
from demos.rollout.sway.classical import classical_black_win_probability

from demos.rollout.epidemic.epidemic_spec import EpidemicSpec
from demos.rollout.epidemic.rollout_oracle import make_epidemic_rollout_oracle
from demos.rollout.epidemic.eval import (
    verify_sampled_branches as verify_epi_branches,
    monte_carlo_payoff_from_oracle as mc_epi_payoff,
)
from demos.rollout.epidemic.classical import classical_epidemic_payoff_exact


@dataclass
class CircuitMetrics:
    qubits: int
    depth: int
    gates: int


def _compile_metrics(spec, factory) -> CircuitMetrics:
    oracle = factory(spec, prepare_superpositions=True)
    prog = oracle.build_exact(*spec.register_specs())
    qc = QiskitBackend().emit(lower_exact_program(prog))
    return CircuitMetrics(qc.num_qubits, qc.depth(), sum(qc.count_ops().values()))


def sway_metrics(rows: int, cols: int, horizon: int) -> CircuitMetrics:
    return _compile_metrics(SwaySpec(rows=rows, cols=cols, horizon=horizon), make_sway_oracle)


def epi_metrics(rows: int, cols: int, horizon: int, threshold: int) -> CircuitMetrics:
    spec = EpidemicSpec(rows=rows, cols=cols, horizon=horizon, threshold=threshold)
    return _compile_metrics(spec, make_epidemic_rollout_oracle)


def _validate_sway(rows: int, cols: int, horizon: int,
                   branch_samples: int, mc_samples: int,
                   seed_branch: int, seed_mc: int) -> None:
    spec = SwaySpec(rows=rows, cols=cols, horizon=horizon)
    t0 = time.time()
    metrics = _compile_metrics(spec, make_sway_oracle)
    matches, total = verify_sway_branches(spec, samples=branch_samples, seed=seed_branch)
    mc, se = mc_sway_payoff(spec, samples=mc_samples, seed=seed_mc)
    exact = classical_black_win_probability(spec)
    elapsed = time.time() - t0
    print(f"Sway   {rows}x{cols} H={horizon:<2}: "
          f"q={metrics.qubits:>5} d={metrics.depth:>6} g={metrics.gates:>7}  "
          f"branch={matches}/{total}  "
          f"MC={mc:.3f}±{1.96*se:.3f}  exact={exact:.3f}  ({elapsed:.1f}s)")


def _validate_epi(rows: int, cols: int, horizon: int, threshold: int,
                  branch_samples: int, mc_samples: int,
                  seed_branch: int, seed_mc: int,
                  do_exact: bool = True) -> None:
    spec = EpidemicSpec(rows=rows, cols=cols, horizon=horizon, threshold=threshold)
    t0 = time.time()
    metrics = _compile_metrics(spec, make_epidemic_rollout_oracle)
    matches, total = verify_epi_branches(spec, samples=branch_samples, seed=seed_branch)
    mc, se = mc_epi_payoff(spec, samples=mc_samples, seed=seed_mc)
    exact_str = f"{classical_epidemic_payoff_exact(spec):.3f}" if do_exact else "-"
    elapsed = time.time() - t0
    print(f"Epi.   {rows}x{cols} H={horizon} T={threshold}: "
          f"q={metrics.qubits:>5} d={metrics.depth:>6} g={metrics.gates:>7}  "
          f"branch={matches}/{total}  "
          f"MC={mc:.3f}±{1.96*se:.3f}  exact={exact_str}  ({elapsed:.1f}s)")


def run_validation(branch_samples: int = 256, mc_samples: int = 1000) -> None:
    print("=== Table 1: validation ===")
    _validate_sway(3, 3, 2, branch_samples, mc_samples, seed_branch=7, seed_mc=11)
    _validate_sway(5, 5, 3, branch_samples, mc_samples, seed_branch=7, seed_mc=11)
    _validate_epi(3, 3, 2, threshold=2,
                  branch_samples=branch_samples, mc_samples=mc_samples,
                  seed_branch=7, seed_mc=11)


def _scale_sway(rows: int, cols: int, horizon: int) -> CircuitMetrics:
    return sway_metrics(rows, cols, horizon)


def _scale_epi(rows: int, cols: int, horizon: int, threshold: int) -> CircuitMetrics:
    return epi_metrics(rows, cols, horizon, threshold)


def run_scaling() -> None:
    print("\n=== Table 2: scaling (qubits / gates) ===")
    print(f"{'m':>3} {'H':>3} {'N':>4}   {'Sway q':>6} {'Epi q':>6}   {'Sway g':>9} {'Epi g':>9}")
    # Epidemic threshold T scales with grid size: payoff = 1 iff final
    # infected count <= T. Setting T = N/5 keeps the success criterion
    # comparable across scales (clamped at 1 for the smallest grid).
    rows = [(5, 5, 25), (7, 5, 49), (10, 5, 100), (10, 10, 100)]
    for m, h, n in rows:
        sw = _scale_sway(m, m, h)
        ep = _scale_epi(m, m, h, threshold=max(1, n // 5))
        print(f"{m:>3} {h:>3} {n:>4}   {sw.qubits:>6} {ep.qubits:>6}   {sw.gates:>9} {ep.gates:>9}")


def main() -> None:
    parser = argparse.ArgumentParser(description="Print validation and scaling tables for the rollout oracle.")
    parser.add_argument("--validate-only", action="store_true")
    parser.add_argument("--scale-only", action="store_true")
    parser.add_argument("--branch-samples", type=int, default=256)
    parser.add_argument("--mc-samples", type=int, default=1000)
    args = parser.parse_args()

    if not args.scale_only:
        run_validation(branch_samples=args.branch_samples, mc_samples=args.mc_samples)
    if not args.validate_only:
        run_scaling()


if __name__ == "__main__":
    main()
