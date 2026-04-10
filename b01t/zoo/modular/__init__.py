"""Modular arithmetic for Shor-class algorithms.

All functions use only permutation gates and are @coherent/@primitive.

  ctrl_modular_add_wires       -- wire-level controlled (b + c) mod N
  make_inplace_modular_mul     -- @primitive |y> -> |ay mod N>
  make_controlled_modular_exp  -- @primitive controlled a^x mod N oracle
"""
from .modular_add import ctrl_modular_add_wires, modular_add_constant_wires
from .modular_mul import make_inplace_modular_mul
from .modular_exp import make_controlled_modular_exp
