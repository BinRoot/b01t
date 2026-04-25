# Rollout Oracle Demos

Coherent rollout oracles for sequential decision problems.

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
