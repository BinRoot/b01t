"""Cuccaro ripple-carry adder (2004) and constant-add helpers.

Wire-level implementation using only permutation gates (cx, ccx, x).
The adder is a self-cleaning permutation: a is preserved, b becomes
the sum, and the carry-in wire is restored to |0>.

Reference: Cuccaro et al., "A new reversible circuit for the full
adder" (quant-ph/0410184).
"""

from b01t.core import DSLValidationError, Wire, cx, ccx, x
from b01t.kit.arithmetic.primitives import int_to_bits


def _maj_wires(x: Wire, y: Wire, z: Wire) -> None:
    """MAJ (majority) gate on three wires.

    Transforms (x, y, z) -> (x XOR z, y XOR z, MAJ(x, y, z)).
    The majority output lands in z.
    """
    cx(z, y)
    cx(z, x)
    ccx(x, y, z)


def _uma_wires(x: Wire, y: Wire, z: Wire) -> None:
    """UMA (unmajority-and-add) gate on three wires.

    Inverse of MAJ, plus sum extraction: restores x and z,
    places the sum bit (x_orig XOR y_orig XOR z_orig) in y.
    """
    ccx(x, y, z)
    cx(z, x)
    cx(x, y)


def ripple_carry_add_wires(
    a_wires: list[Wire],
    b_wires: list[Wire],
    cin: Wire,
) -> None:
    """Cuccaro ripple-carry adder (wire-level).

    Computes b <- a + b (mod 2^n) in-place.

    After execution:
      a_wires: restored to original values
      b_wires: holds (a + b) mod 2^n
      cin:     restored to |0>

    All gates are cx, ccx (permutation gates).
    The carry-out (overflow) is not preserved.

    Args:
        a_wires: n-bit first operand (preserved)
        b_wires: n-bit second operand (becomes sum)
        cin:     carry-in wire, must start at |0>, returned to |0>
    """
    n = len(a_wires)
    if len(b_wires) != n:
        raise DSLValidationError("a and b must have same width")
    if n == 0:
        return

    # Forward MAJ sweep: propagate carries through a wires
    _maj_wires(cin, b_wires[0], a_wires[0])
    for i in range(1, n):
        _maj_wires(a_wires[i - 1], b_wires[i], a_wires[i])

    # Reverse UMA sweep: extract sum bits into b, restore a and cin
    for i in range(n - 1, 0, -1):
        _uma_wires(a_wires[i - 1], b_wires[i], a_wires[i])
    _uma_wires(cin, b_wires[0], a_wires[0])


def controlled_add_wires(
    ctrl: Wire,
    a_wires: list[Wire],
    b_wires: list[Wire],
    cin: Wire,
) -> None:
    """Controlled ripple-carry adder (wire-level).

    Computes b <- b + a (mod 2^n) only when ctrl = |1>.
    When ctrl = |0>, all registers are unchanged.

    Uses the Cuccaro structure with Toffoli gates upgraded to
    doubly-controlled where the ctrl wire is added.

    This is a simple implementation that wraps each gate with the
    control. More optimized versions exist but this is correct and
    uses only permutation gates.

    Args:
        ctrl:    control wire
        a_wires: n-bit first operand (preserved)
        b_wires: n-bit second operand (becomes sum when ctrl=1)
        cin:     carry-in wire, must start at |0>, returned to |0>
    """
    # For a controlled adder, we use the fact that the Cuccaro adder
    # only modifies b (permanently). We can implement controlled-add
    # by running the adder, then conditionally swapping b back.
    # But that requires extra ancilla.
    #
    # A simpler approach: the CX gates in MAJ/UMA don't need control
    # (they only modify scratch state temporarily). Only the CCX gates
    # that contribute to the final carry/sum need the control.
    #
    # For now, use the straightforward approach: run the full adder
    # only when ctrl is set, by replacing each gate with its controlled
    # variant. This gives correct results but uses MCX (3-controlled)
    # gates.
    #
    # TODO: optimize with a dedicated controlled-Cuccaro circuit.
    from b01t.core import mcx

    def _cmaj(c: Wire, x: Wire, y: Wire, z: Wire) -> None:
        """Controlled MAJ: only acts when c = |1>."""
        ccx(c, z, y)
        ccx(c, z, x)
        mcx([c, x, y], z)

    def _cuma(c: Wire, x: Wire, y: Wire, z: Wire) -> None:
        """Controlled UMA: only acts when c = |1>."""
        mcx([c, x, y], z)
        ccx(c, z, x)
        ccx(c, x, y)

    n = len(a_wires)
    if len(b_wires) != n:
        raise DSLValidationError("a and b must have same width")

    if n == 0:
        return

    _cmaj(ctrl, cin, b_wires[0], a_wires[0])
    for i in range(1, n):
        _cmaj(ctrl, a_wires[i - 1], b_wires[i], a_wires[i])

    for i in range(n - 1, 0, -1):
        _cuma(ctrl, a_wires[i - 1], b_wires[i], a_wires[i])
    _cuma(ctrl, cin, b_wires[0], a_wires[0])


# ---------------------------------------------------------------------------
# Carry-out variant
# ---------------------------------------------------------------------------

def ripple_carry_add_with_carry_wires(
    a_wires: list[Wire],
    b_wires: list[Wire],
    cin: Wire,
    cout: Wire,
) -> None:
    """Cuccaro adder that also captures the carry-out.

    After execution:
      a_wires: restored
      b_wires: (a + b) mod 2^n
      cin:     restored to |0>
      cout:    XORed with carry-out (1 if a+b >= 2^n)

    The carry is captured between the MAJ and UMA sweeps, when it
    sits in a_wires[n-1].
    """
    n = len(a_wires)
    if len(b_wires) != n:
        raise DSLValidationError("a and b must have same width")
    if n == 0:
        return

    _maj_wires(cin, b_wires[0], a_wires[0])
    for i in range(1, n):
        _maj_wires(a_wires[i - 1], b_wires[i], a_wires[i])

    # Capture carry-out (a_wires[n-1] holds it after MAJ sweep)
    cx(a_wires[n - 1], cout)

    for i in range(n - 1, 0, -1):
        _uma_wires(a_wires[i - 1], b_wires[i], a_wires[i])
    _uma_wires(cin, b_wires[0], a_wires[0])


# ---------------------------------------------------------------------------
# Classical-constant addition/subtraction
# ---------------------------------------------------------------------------

def add_constant_wires(
    b_wires: list[Wire],
    value: int,
    const_wires: list[Wire],
    cin: Wire,
) -> None:
    """Add a classical constant to quantum register b.

    b <- b + value (mod 2^n).

    Loads value into const_wires (ancilla), uses Cuccaro adder
    (which preserves 'a'), then unloads. const_wires and cin are
    restored to |0>.

    Args:
        b_wires:     n-bit quantum register (becomes b + value)
        value:       classical integer to add
        const_wires: n ancilla wires (must start at |0>, restored to |0>)
        cin:         carry-in wire (must start at |0>, restored to |0>)
    """
    n = len(b_wires)
    if len(const_wires) != n:
        raise DSLValidationError("const_wires must match b_wires width")
    bits = int_to_bits(value % (1 << n), n)

    # Load constant
    for i in range(n):
        if bits[i]:
            x(const_wires[i])

    # Add (Cuccaro preserves const_wires = 'a')
    ripple_carry_add_wires(const_wires, b_wires, cin)

    # Unload constant
    for i in range(n):
        if bits[i]:
            x(const_wires[i])


def add_constant_with_carry_wires(
    b_wires: list[Wire],
    value: int,
    const_wires: list[Wire],
    cin: Wire,
    cout: Wire,
) -> None:
    """Add classical constant to b, XOR carry-out into cout.

    Same as add_constant_wires but also captures the carry-out.
    cout is XORed (not set) so it can be used to toggle a flag.
    """
    n = len(b_wires)
    if len(const_wires) != n:
        raise DSLValidationError("const_wires must match b_wires width")
    bits = int_to_bits(value % (1 << n), n)

    for i in range(n):
        if bits[i]:
            x(const_wires[i])

    ripple_carry_add_with_carry_wires(const_wires, b_wires, cin, cout)

    for i in range(n):
        if bits[i]:
            x(const_wires[i])


def sub_constant_wires(
    b_wires: list[Wire],
    value: int,
    const_wires: list[Wire],
    cin: Wire,
) -> None:
    """Subtract a classical constant from quantum register b.

    b <- b - value (mod 2^n).

    Implemented as b + (2^n - value) mod 2^n.
    """
    n = len(b_wires)
    complement = (1 << n) - (value % (1 << n))
    add_constant_wires(b_wires, complement % (1 << n), const_wires, cin)


def sub_constant_with_carry_wires(
    b_wires: list[Wire],
    value: int,
    const_wires: list[Wire],
    cin: Wire,
    cout: Wire,
) -> None:
    """Subtract classical constant from b, XOR borrow into cout.

    cout is XORed with 1 if b >= value (no borrow), 0 if b < value.
    """
    n = len(b_wires)
    complement = (1 << n) - (value % (1 << n))
    add_constant_with_carry_wires(b_wires, complement % (1 << n),
                                  const_wires, cin, cout)
