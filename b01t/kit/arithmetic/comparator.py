"""Unsigned less-than comparator: |a>|b>|0> -> |a>|b>|a<b>.

Uses a borrow-chain approach: propagate borrows from a - b, with the
final borrow indicating a < b. The borrow chain is kept entirely in
ancilla wires, so the apply block (which copies the result) is system-
disjoint from compute, satisfying b01t's PreservesFirst condition.

All gates are permutation gates (x, cx, ccx).
"""

from b01t.core import DSLValidationError, QReg, Wire, coherent, cx, ccx, x
from b01t.kit import ancilla, compute, apply, uncompute


def _borrow_chain_wires(
    a_wires: list[Wire],
    b_wires: list[Wire],
    borrow_wires: list[Wire],
) -> None:
    """Compute the borrow chain of a - b into ancilla borrow wires.

    borrow_wires[i] = 1 iff a[0..i-1] < b[0..i-1] (unsigned).
    All borrow wires must start at |0>.
    a and b wires are used as controls and temporarily flipped, then
    restored; they are unchanged after this function.

    Args:
        a_wires: n-bit first operand (preserved)
        b_wires: n-bit second operand (preserved)
        borrow_wires: n wires, borrow[i] receives borrow for bit i+1.
                      borrow_wires[-1] = (a < b).
    """
    n = len(a_wires)
    if len(b_wires) != n:
        raise DSLValidationError("a_wires and b_wires must have the same width")
    if len(borrow_wires) != n:
        raise DSLValidationError("borrow_wires must match operand width")
    if n == 0:
        raise DSLValidationError("comparator requires non-empty input registers")

    # Bit 0: borrow[0] = (NOT a[0]) AND b[0]
    # (no previous borrow, carry-in is 0)
    x(a_wires[0])
    ccx(a_wires[0], b_wires[0], borrow_wires[0])
    x(a_wires[0])

    # Bits 1..n-1: borrow[i] = MAJ(NOT a[i], b[i], borrow[i-1])
    # = (NOT a[i])·b[i] XOR (NOT a[i])·borrow[i-1] XOR b[i]·borrow[i-1]
    for i in range(1, n):
        x(a_wires[i])
        ccx(a_wires[i], b_wires[i], borrow_wires[i])
        ccx(a_wires[i], borrow_wires[i - 1], borrow_wires[i])
        x(a_wires[i])
        ccx(b_wires[i], borrow_wires[i - 1], borrow_wires[i])


@coherent
def less_than(a: QReg, b: QReg, result: QReg):
    """Set result[0] = 1 iff a < b (unsigned). a and b are preserved.

    Uses compute/apply/uncompute with n ancilla qubits for the borrow
    chain. The apply block copies the final borrow to result, touching
    only ancilla (control) and result (target), disjoint from compute's
    system wires.

    Args:
        a: n-bit register (preserved)
        b: n-bit register (preserved)
        result: 1-bit register, must start at |0>, set to |a < b>
    """
    n = len(a)
    with ancilla(n) as borrow:
        compute(lambda: _borrow_chain_wires(
            a.wires(), b.wires(), borrow.wires()))
        apply(lambda: cx(borrow[n - 1], result[0]))
        uncompute()
