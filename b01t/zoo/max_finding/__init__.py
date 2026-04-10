"""Quantum maximum finding via Durr-Hoyer algorithm.

Composes coherent amplitude estimation with Grover search to find
the arm with highest payoff probability in O(sqrt(k)/eps) oracle calls.
"""
from .comparison_oracle import make_comparison_oracle
from .durr_hoyer import DurrHoyerRunner, make_search_step
