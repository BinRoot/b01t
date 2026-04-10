# Rollout Oracle Demos

Coherent rollout oracles for sequential decision problems.

- `sway/` - two-player stochastic board game
- `epidemic/` - SIR epidemic intervention model

## Run

```bash
uv run pytest tests/test_rollout_sway.py              # sway oracle
uv run pytest tests/test_rollout_epidemic.py          # epidemic oracle
uv run pytest tests/test_best_arm_correctness.py      # AE picks the right action
uv run python -m demos.best_arm.demo                  # full pipeline: oracle -> AE -> max-finding
```
