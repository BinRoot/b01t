"""Quantum Phase Estimation (QPE).

@parametric because it uses inverse QFT (which has continuous rotations).
Takes an arbitrary controlled-unitary oracle and estimates its eigenvalues.
"""
from .qpe import make_qpe
