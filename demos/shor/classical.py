"""Classical post-processing for Shor's algorithm.

Given a measurement outcome from the QPE circuit, use continued
fractions to extract the period r of a^r = 1 (mod N).
"""

import math


def continued_fraction_convergents(numerator: int, denominator: int):
    """Yield convergents p/q of numerator/denominator."""
    if denominator == 0:
        return
    a = numerator // denominator
    p_prev, p_curr = 1, a
    q_prev, q_curr = 0, 1
    yield p_curr, q_curr

    num, den = denominator, numerator - a * denominator
    while den > 0:
        a = num // den
        p_prev, p_curr = p_curr, a * p_curr + p_prev
        q_prev, q_curr = q_curr, a * q_curr + q_prev
        yield p_curr, q_curr
        num, den = den, num - a * den


def extract_period(measurement: int, num_counting_bits: int, N: int) -> int | None:
    """Extract period r from a QPE measurement outcome.

    The measurement approximates s/r * 2^t where t = num_counting_bits.
    We use continued fractions to find r.

    Returns r if found (and r > 0, r < N), else None.
    """
    Q = 1 << num_counting_bits
    if measurement == 0:
        return None

    best_q = None
    for _, q in continued_fraction_convergents(measurement, Q):
        if 1 < q < N:
            best_q = q

    return best_q


def find_period_classical(a: int, N: int) -> int:
    """Classically find the period r: a^r = 1 (mod N).

    Brute-force for small N. Used for testing.
    """
    r = 1
    val = a % N
    while val != 1 and r < N:
        val = (val * a) % N
        r += 1
    return r if val == 1 else -1


def factor_from_period(a: int, r: int, N: int) -> tuple[int, int] | None:
    """Given the period r of a mod N, attempt to find a factor of N.

    If r is even and a^(r/2) != -1 (mod N), then
    gcd(a^(r/2) +/- 1, N) may yield a non-trivial factor.
    """
    if r % 2 != 0:
        return None

    half = pow(a, r // 2, N)
    if half == N - 1:
        return None

    f1 = math.gcd(half - 1, N)
    f2 = math.gcd(half + 1, N)

    if 1 < f1 < N:
        return f1, N // f1
    if 1 < f2 < N:
        return f2, N // f2
    return None
