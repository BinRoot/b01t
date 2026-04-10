"""Quantum Fourier Transform and inverse.

@parametric because CRZ gates use continuous rotation angles.
No ancilla is needed; it operates entirely on system qubits.
"""
from .qft import qft, inverse_qft
