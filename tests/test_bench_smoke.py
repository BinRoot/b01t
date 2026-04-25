"""Smoke test for demos.rollout.bench: tiny instances run without error."""
from demos.rollout.bench import (
    epi_metrics,
    sway_metrics,
)


class TestBenchSmoke:
    def test_sway_compile(self):
        m = sway_metrics(2, 2, 1)
        assert m.qubits > 0 and m.gates > 0

    def test_epi_compile(self):
        m = epi_metrics(3, 3, 1, threshold=2)
        assert m.qubits > 0 and m.gates > 0
