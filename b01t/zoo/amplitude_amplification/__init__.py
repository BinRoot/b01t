"""Amplitude amplification: generalized Grover.

Takes an arbitrary state-preparation A and predicate oracle O_chi,
and amplifies the amplitude of "good" states.

  zero_state_reflection    -- @coherent S_0 = 2|0><0| - I
  make_amplification_step  -- @coherent single Q = A S_0 A† O_chi iteration
  make_amplitude_amplifier -- @coherent repeated iterations
"""
from .diffusion import zero_state_reflection
from .amplify import make_amplification_step, make_amplitude_amplifier
