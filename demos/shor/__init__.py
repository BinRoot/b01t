"""Shor's factoring algorithm.

Composes zoo modules (QPE + modular exponentiation) with classical
post-processing (continued fractions for period extraction).

  make_shor_circuit(a, N, t)  -- @adaptive QPE + measurement
  find_period(a, N)           -- classical wrapper: run circuit, extract period
"""
from .circuit import make_shor_circuit
from .classical import find_period_classical
