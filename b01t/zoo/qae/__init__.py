"""Quantum Amplitude Estimation.

Building blocks:
  zero_state_reflection  -- @coherent S_0 = 2|0><0| - I (shared with amplitude_amplification)
  make_qae_round         -- @adaptive single measurement at depth k
  make_qae_schedule      -- list of @adaptive circuits for iterative QAE

Classical post-processing:
  simulate_qae           -- analytically simulate QAE measurements
  ml_estimate            -- grid-search MLE over theta
  clopper_pearson        -- 95% confidence interval
"""
from .diffusion import zero_state_reflection
from .estimation import simulate_qae, ml_estimate, clopper_pearson
from .qae_circuit import make_qae_round, make_qae_schedule
from .coherent_ae import make_coherent_ae
