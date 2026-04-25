"""Branch-agreement and exact-value checks for the epidemic rollout harness."""
from demos.rollout.epidemic.classical import classical_epidemic_payoff_exact
from demos.rollout.epidemic.epidemic_spec import EpidemicSpec
from demos.rollout.epidemic.eval import (
    monte_carlo_payoff_from_oracle,
    verify_sampled_branches,
)


def _spec_3x3_h1_t2() -> EpidemicSpec:
    return EpidemicSpec(rows=3, cols=3, horizon=1, threshold=2, initial_infected=(4,))


def _spec_3x3_h2_t2() -> EpidemicSpec:
    return EpidemicSpec(rows=3, cols=3, horizon=2, threshold=2, initial_infected=(4,))


class TestEpidemicClassical:
    def test_h1_exact(self):
        assert abs(classical_epidemic_payoff_exact(_spec_3x3_h1_t2()) - 0.835) < 1e-3

    def test_h2_exact_matches_paper(self):
        assert abs(classical_epidemic_payoff_exact(_spec_3x3_h2_t2()) - 0.667) < 1e-3


class TestEpidemicBranchAgreement:
    def test_h1(self):
        matches, total = verify_sampled_branches(_spec_3x3_h1_t2(), samples=32, seed=7)
        assert matches == total

    def test_h2(self):
        matches, total = verify_sampled_branches(_spec_3x3_h2_t2(), samples=32, seed=7)
        assert matches == total


class TestEpidemicMonteCarlo:
    def test_h2_within_paper_ci(self):
        spec = _spec_3x3_h2_t2()
        p, _ = monte_carlo_payoff_from_oracle(spec, samples=1000, seed=11)
        # Paper Table 1 row 3: MC = 0.664±0.029 with the same RNG.
        assert abs(p - 0.664) < 1e-3
