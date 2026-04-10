"""Iterative QAE: simulation, MLE, confidence intervals.

These are pure classical functions with no quantum circuits.
"""

import math
import random


def simulate_qae(
    exact_pf: float,
    max_depth: int = 6,
    shots_per_depth: int = 200,
    seed: int = 42,
) -> list[tuple[int, int, int]]:
    """Simulate QAE measurement outcomes analytically.

    Returns list of (depth_k, successes, total_shots).
    """
    theta = math.asin(math.sqrt(exact_pf))
    measurements = []
    for k in range(max_depth + 1):
        p = math.sin((2 * k + 1) * theta) ** 2
        rng = random.Random(seed + k)
        successes = sum(1 for _ in range(shots_per_depth) if rng.random() < p)
        measurements.append((k, successes, shots_per_depth))
    return measurements


def ml_estimate(measurements: list[tuple[int, int, int]]) -> float:
    """Grid-search MLE over theta in [0, pi/2]."""
    best_theta = 0.0
    best_ll = float('-inf')
    for step in range(1, 1000):
        theta = step * math.pi / (2 * 1000)
        ll = 0.0
        for k, s, n in measurements:
            p = math.sin((2 * k + 1) * theta) ** 2
            p = max(1e-12, min(1 - 1e-12, p))
            ll += s * math.log(p) + (n - s) * math.log(1 - p)
        if ll > best_ll:
            best_ll = ll
            best_theta = theta
    return best_theta


def _binom_cdf(k: int, n: int, p: float) -> float:
    """Compute P[X <= k] for X ~ Binomial(n, p)."""
    if k < 0:
        return 0.0
    if k >= n:
        return 1.0
    if p <= 0.0:
        return 1.0
    if p >= 1.0:
        return 0.0

    q = 1.0 - p
    # Start with PMF(0) = q^n and build PMF(i+1) from PMF(i).
    pmf = q**n
    cdf = pmf
    ratio = p / q
    for i in range(0, k):
        pmf *= ((n - i) / (i + 1)) * ratio
        cdf += pmf
    return min(1.0, max(0.0, cdf))


def _invert_binom_cdf_for_p(k: int, n: int, target: float, iters: int = 80) -> float:
    """Solve Binomial CDF equation CDF(k; n, p) = target for p in [0, 1]."""
    lo = 0.0
    hi = 1.0
    for _ in range(iters):
        mid = (lo + hi) / 2.0
        cdf = _binom_cdf(k, n, mid)
        # CDF(k; n, p) is monotone decreasing in p.
        if cdf > target:
            lo = mid
        else:
            hi = mid
    return (lo + hi) / 2.0


def clopper_pearson(successes: int, trials: int) -> tuple[float, float]:
    """Exact two-sided 95% Clopper-Pearson confidence interval for a binomial rate."""
    if trials < 0:
        raise ValueError("trials must be non-negative")
    if successes < 0 or successes > trials:
        raise ValueError("successes must satisfy 0 <= successes <= trials")
    if trials == 0:
        return (0.0, 1.0)
    alpha = 0.05

    if successes == 0:
        lower = 0.0
    else:
        # Lower bound = BetaInv(alpha/2; s, n-s+1), solved via CDF(s-1)=1-alpha/2.
        lower = _invert_binom_cdf_for_p(successes - 1, trials, 1.0 - alpha / 2.0)

    if successes == trials:
        upper = 1.0
    else:
        # Upper bound = BetaInv(1-alpha/2; s+1, n-s), solved via CDF(s)=alpha/2.
        upper = _invert_binom_cdf_for_p(successes, trials, alpha / 2.0)

    return (lower, upper)
