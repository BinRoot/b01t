"""Deutsch's algorithm: the first quantum algorithm.

  make_deutsch_oracle(f0, f1)     @coherent oracle for verification
  make_deutsch_algorithm(f0, f1)  @adaptive full algorithm with measurement
"""
from .oracle import make_deutsch_oracle
from .algorithm import make_deutsch_algorithm
