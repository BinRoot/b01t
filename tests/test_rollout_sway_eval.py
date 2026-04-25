"""Branch-agreement and exact-value checks for the Sway rollout harness."""
from demos.rollout.sway.classical import classical_black_win_probability
from demos.rollout.sway.eval import (
    monte_carlo_payoff_from_oracle,
    verify_sampled_branches,
)
from demos.rollout.sway.sway_spec import SwaySpec


class TestSwayClassical:
    def test_2x2_h1_exact(self):
        assert abs(classical_black_win_probability(SwaySpec(2, 2, 1)) - 0.16) < 1e-6

    def test_3x3_h1_exact(self):
        assert abs(classical_black_win_probability(SwaySpec(3, 3, 1)) - 0.16) < 1e-6

    def test_3x3_h2_exact_matches_paper(self):
        assert abs(classical_black_win_probability(SwaySpec(3, 3, 2)) - 0.271) < 1e-3


class TestSwayBranchAgreement:
    def test_2x2_h1(self):
        matches, total = verify_sampled_branches(SwaySpec(2, 2, 1), samples=64, seed=7)
        assert matches == total

    def test_3x3_h1(self):
        matches, total = verify_sampled_branches(SwaySpec(3, 3, 1), samples=32, seed=7)
        assert matches == total

    def test_3x3_h2(self):
        matches, total = verify_sampled_branches(SwaySpec(3, 3, 2), samples=32, seed=7)
        assert matches == total


class TestSwayMonteCarlo:
    def test_3x3_h2_within_paper_ci(self):
        spec = SwaySpec(3, 3, 2)
        p, _ = monte_carlo_payoff_from_oracle(spec, samples=1000, seed=11)
        # Paper Table 1 row 1: MC = 0.281±0.028 with the same RNG.
        assert abs(p - 0.281) < 1e-3
