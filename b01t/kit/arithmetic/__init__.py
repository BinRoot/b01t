"""Reversible arithmetic primitives: increment, decrement, addition, comparison."""
from .primitives import (
    controlled_inc,
    controlled_dec,
    apply_pattern_x_wires,
    int_to_bits,
    controlled_inc_wires,
    controlled_dec_wires,
    binary_controlled_fan,
)
from .adder import (
    ripple_carry_add_wires,
    ripple_carry_add_with_carry_wires,
    controlled_add_wires,
    add_constant_wires,
    add_constant_with_carry_wires,
    sub_constant_wires,
    sub_constant_with_carry_wires,
)
from .comparator import (
    less_than,
)
