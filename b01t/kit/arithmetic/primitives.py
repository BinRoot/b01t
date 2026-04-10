"""Controlled arithmetic primitives.

All subroutines use only permutation gates (x, cx, ccx, mcx).
These are reversible classical logic building blocks.

@coherent: pure reversible transformations on system registers (no scratch).
Wire-level helpers are plain functions usable inside any build context.
"""

from typing import Sequence

from b01t.core import QReg, Wire, coherent, cx, ccx, mcx, x


@coherent
def controlled_inc(ctrl: QReg, reg: QReg):
    """Increment w-bit register by 1 when ctrl[0] = |1>."""
    w = len(reg)
    for i in reversed(range(w)):
        controls = [ctrl[0]] + [reg[j] for j in range(i)]
        if len(controls) == 1:
            cx(controls[0], reg[i])
        elif len(controls) == 2:
            ccx(controls[0], controls[1], reg[i])
        else:
            mcx(controls, reg[i])


@coherent
def controlled_dec(ctrl: QReg, reg: QReg):
    """Decrement w-bit register by 1 when ctrl[0] = |1>."""
    w = len(reg)
    for i in range(w):
        controls = [ctrl[0]] + [reg[j] for j in range(i)]
        if len(controls) == 1:
            cx(controls[0], reg[i])
        elif len(controls) == 2:
            ccx(controls[0], controls[1], reg[i])
        else:
            mcx(controls, reg[i])


def apply_pattern_x_wires(
    control_wires: list[Wire],
    pattern: list[int],
    target: Wire,
) -> None:
    """Flip target iff control_wires match the given bit pattern."""
    for i, bit in enumerate(pattern):
        if bit == 0:
            x(control_wires[i])
    if len(control_wires) == 1:
        cx(control_wires[0], target)
    elif len(control_wires) == 2:
        ccx(control_wires[0], control_wires[1], target)
    else:
        mcx(control_wires, target)
    for i, bit in enumerate(pattern):
        if bit == 0:
            x(control_wires[i])


def int_to_bits(value: int, width: int) -> list[int]:
    """Convert integer to LSB-first bit list."""
    return [(value >> i) & 1 for i in range(width)]


def controlled_inc_wires(ctrl: Wire, reg_wires: list[Wire]) -> None:
    """Increment reg_wires by 1 when ctrl = |1>. Wire-level."""
    w = len(reg_wires)
    for i in reversed(range(w)):
        controls = [ctrl] + reg_wires[:i]
        if len(controls) == 1:
            cx(controls[0], reg_wires[i])
        elif len(controls) == 2:
            ccx(controls[0], controls[1], reg_wires[i])
        else:
            mcx(controls, reg_wires[i])


def controlled_dec_wires(ctrl: Wire, reg_wires: list[Wire]) -> None:
    """Decrement reg_wires by 1 when ctrl = |1>. Wire-level."""
    w = len(reg_wires)
    for i in range(w):
        controls = [ctrl] + reg_wires[:i]
        if len(controls) == 1:
            cx(controls[0], reg_wires[i])
        elif len(controls) == 2:
            ccx(controls[0], controls[1], reg_wires[i])
        else:
            mcx(controls, reg_wires[i])


def binary_controlled_fan(
    index_wires: list[Wire],
    target_wires: list[Wire],
    n_valid: int,
) -> None:
    """Decode a binary index to flip the indexed target wire.

    For each i in [0, n_valid): MCX(index==i, target[i]).
    Uses Gray code ordering to minimize X gate overhead.

    Equivalent to calling apply_pattern_x_wires for each cell,
    but with O(2^w) X gates total instead of O(n_valid * w).
    """
    w = len(index_wires)
    total = 1 << w

    # Gray code: gc(i) = i ^ (i >> 1)
    prev_bits: list[int] | None = None
    for g in range(total):
        gc = g ^ (g >> 1)
        cur_bits = int_to_bits(gc, w)
        if prev_bits is None:
            # Setup: X where bit is 0
            for bit in range(w):
                if cur_bits[bit] == 0:
                    x(index_wires[bit])
        else:
            # Transition: flip the one bit that changed
            for bit in range(w):
                if cur_bits[bit] != prev_bits[bit]:
                    x(index_wires[bit])
                    break
        prev_bits = cur_bits
        # Apply MCX only for valid cells
        if gc < n_valid:
            if w == 1:
                cx(index_wires[0], target_wires[gc])
            elif w == 2:
                ccx(index_wires[0], index_wires[1], target_wires[gc])
            else:
                mcx(index_wires, target_wires[gc])
    # Cleanup: undo remaining X gates
    if prev_bits is not None:
        for bit in range(w):
            if prev_bits[bit] == 0:
                x(index_wires[bit])
