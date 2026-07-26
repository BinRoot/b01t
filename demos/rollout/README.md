# Rollout Oracle Demos

Coherent rollout oracles for sequential decision problems.

## Publication

This directory is the artifact for:

> Nishant Shukla. **Coherent Rollout Oracles for Finite-Horizon
> Sequential Decision Problems.** IEEE International Conference on
> Quantum Computing and Engineering (QCE), 2026.

The code behind the paper's tables and proofs is pinned at tag
[`v0.1.0`](https://github.com/BinRoot/b01t/tree/v0.1.0/demos/rollout).

```bibtex
@inproceedings{shukla2026rollout,
  author    = {Shukla, Nishant},
  title     = {Coherent Rollout Oracles for Finite-Horizon Sequential
               Decision Problems},
  booktitle = {IEEE International Conference on Quantum Computing and
               Engineering (QCE)},
  year      = {2026}
}
```

- `sway/` - two-player stochastic game
- `epidemic/` - SIR epidemic intervention model
- `bench.py` - validation and scaling tables for the construction
- `RolloutProofs/` - Lean 4 machine-checked proofs of the construction's theorems

## Run

```bash
uv run pytest tests/test_rollout_sway.py              # sway oracle
uv run pytest tests/test_rollout_epidemic.py          # epidemic oracle
uv run pytest tests/test_best_arm_correctness.py      # AE picks the right action
uv run python -m demos.best_arm.demo                  # full pipeline: oracle -> AE -> max-finding
uv run python -m demos.rollout.bench                  # validation + scaling tables
```

## Proofs

```bash
cd RolloutProofs && lake exe cache get && lake build
```

See `RolloutProofs/README.md` for the theorem-to-module map.
