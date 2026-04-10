"""Modular addition of a classical constant: b <- (b + c) mod N.

Wire-level helper using only permutation gates (x, cx, ccx).
The constant c is loaded conditionally via CX(ctrl, const[i]), so the
same function serves as both plain and controlled modular add.

Algorithm (VBE-style):
  1. b <- b + c             (capture carry in flag)
  2. b <- b - N             (capture borrow XOR in flag)
  3. if flag=0: b <- b + N  (undo subtraction if b+c >= N was correct)
  4. clean flag              (subtract c, check carry, re-add c)
"""

from b01t.core import Wire, x, cx
from b01t.kit.arithmetic.adder import (
    ripple_carry_add_wires,
    ripple_carry_add_with_carry_wires,
    controlled_add_wires,
)
from b01t.kit.arithmetic.primitives import int_to_bits


def _load_constant(ctrl: Wire | None, const_wires: list[Wire], value: int) -> None:
    """Load classical value into const_wires. If ctrl given, load conditionally."""
    n = len(const_wires)
    bits = int_to_bits(value % (1 << n), n)
    for i in range(n):
        if bits[i]:
            if ctrl is not None:
                cx(ctrl, const_wires[i])
            else:
                x(const_wires[i])


def ctrl_modular_add_wires(
    ctrl: Wire,
    b_wires: list[Wire],
    c: int,
    N: int,
    const_wires: list[Wire],
    cin: Wire,
    flag: Wire,
) -> None:
    """Controlled modular add: b <- (b + c) mod N when ctrl=|1>.

    When ctrl=|0>, all wires are unchanged (constants load as 0).

    Preconditions: 0 <= b < N, 0 <= c < N, N > 0.

    Args:
        ctrl:        control wire
        b_wires:     n-bit quantum register (modified in-place)
        c:           classical constant to add
        N:           classical modulus
        const_wires: n ancilla wires for loading constants (restored to |0>)
        cin:         1 ancilla wire for carry (restored to |0>)
        flag:        1 ancilla wire for overflow flag (restored to |0>)
    """
    n = len(b_wires)
    comp_N = (1 << n) - (N % (1 << n))  # 2^n - N (for subtraction)
    comp_c = (1 << n) - (c % (1 << n))  # 2^n - c (for subtraction)

    # Step 1: b <- b + c, carry -> flag
    _load_constant(ctrl, const_wires, c)
    ripple_carry_add_with_carry_wires(const_wires, b_wires, cin, flag)
    _load_constant(ctrl, const_wires, c)  # unload

    # Step 2: b <- b - N (add 2^n - N), borrow -> flag (XOR)
    _load_constant(ctrl, const_wires, comp_N)
    ripple_carry_add_with_carry_wires(const_wires, b_wires, cin, flag)
    _load_constant(ctrl, const_wires, comp_N)  # unload

    # Step 3: if flag=0 (b+c >= N, reduction was correct), do nothing.
    #         if flag=1 could NOT happen in correct case... let me re-derive.
    # After steps 1+2: flag = carry1 XOR carry2.
    #   Case b+c < N: carry1=0, carry2=0 → flag=0. b'' = b+c-N+2^n. Need +N.
    #   Case N <= b+c < 2^n: carry1=0, carry2=1 → flag=1. b'' = b+c-N. Correct.
    #   Case b+c >= 2^n: carry1=1, carry2=0 → flag=1. b'' = b+c-N. Correct.
    # So: add N back when flag=0.
    _load_constant(ctrl, const_wires, N)
    x(flag)
    controlled_add_wires(flag, const_wires, b_wires, cin)
    x(flag)
    _load_constant(ctrl, const_wires, N)  # unload

    # Step 4: clean flag.
    # b = (b+c) mod N. We sub c, XOR carry into flag, then re-add c.
    #   If original b+c < N: b_final=b+c. sub c: b+c-c=b >= 0 → carry=1. flag=0 XOR 1=1? No.
    #   Wait: flag after step 3:
    #     Case b+c < N: flag was 0. After x(flag) and controlled_add, flag got X'd twice → back to 0.
    #     Case b+c >= N: flag was 1. After x(flag)→0, controlled_add doesn't fire, x(flag)→1.
    #   So after step 3: flag = 0 if b+c < N, flag = 1 if b+c >= N.
    #
    #   sub c with carry XOR into flag:
    #     Case b+c < N: b_final=b+c. sub c: carry=1 (b+c >= c). flag = 0 XOR 1 = 1.
    #     Case b+c >= N: b_final=b+c-N. sub c: is b+c-N >= c? b+c-N >= c iff b >= N+c-c=N.
    #       But b < N. So b+c-N < N ≤ N. If c > 0: b+c-N could be < c.
    #       Carry = 1 if (b+c-N) + (2^n - c) >= 2^n, i.e. b+c-N >= c, i.e. b >= N. But b < N. → carry=0.
    #       flag = 1 XOR 0 = 1.
    #   Both cases: flag = 1. Then we need one more XOR to get flag = 0.
    # Hmm, that gives flag = 1 in both cases, not 0.
    #
    # Let me try: use add (not sub) of (2^n - c) to get the subtraction with carry:
    _load_constant(ctrl, const_wires, comp_c)
    ripple_carry_add_with_carry_wires(const_wires, b_wires, cin, flag)
    _load_constant(ctrl, const_wires, comp_c)  # unload
    # flag now = previous XOR carry_of_sub_c.
    #   Case b+c < N: flag = 0 XOR 1 = 1
    #   Case b+c >= N: flag = 1 XOR 0 = 1
    # flag = 1 in both cases! Need to flip it.
    # Actually wait, when ctrl=0: flag never changed from 0. We'd flip to 1. Bad.
    # So we can't just X(flag). We need a controlled flip.
    # But actually when ctrl=0, ALL steps were no-ops (constants loaded as 0,
    # adding 0 gives carry=0, flag stays 0). The sub step also adds 0 with carry=0.
    # So flag = 0 when ctrl=0.
    # When ctrl=1: flag = 1. So we do CX(ctrl, flag) to clean it.
    cx(ctrl, flag)

    # Restore b: add c back
    _load_constant(ctrl, const_wires, c)
    ripple_carry_add_wires(const_wires, b_wires, cin)
    _load_constant(ctrl, const_wires, c)  # unload


def modular_add_constant_wires(
    b_wires: list[Wire],
    c: int,
    N: int,
    const_wires: list[Wire],
    cin: Wire,
    flag: Wire,
) -> None:
    """Uncontrolled modular add: b <- (b + c) mod N.

    Same as ctrl_modular_add_wires but without a control wire.
    Constants are loaded unconditionally.
    """
    n = len(b_wires)
    comp_N = (1 << n) - (N % (1 << n))
    comp_c = (1 << n) - (c % (1 << n))

    # Step 1: add c
    _load_constant(None, const_wires, c)
    ripple_carry_add_with_carry_wires(const_wires, b_wires, cin, flag)
    _load_constant(None, const_wires, c)

    # Step 2: sub N
    _load_constant(None, const_wires, comp_N)
    ripple_carry_add_with_carry_wires(const_wires, b_wires, cin, flag)
    _load_constant(None, const_wires, comp_N)

    # Step 3: add N back if flag=0
    _load_constant(None, const_wires, N)
    x(flag)
    controlled_add_wires(flag, const_wires, b_wires, cin)
    x(flag)
    _load_constant(None, const_wires, N)

    # Step 4: clean flag
    _load_constant(None, const_wires, comp_c)
    ripple_carry_add_with_carry_wires(const_wires, b_wires, cin, flag)
    _load_constant(None, const_wires, comp_c)
    x(flag)

    # Restore b
    _load_constant(None, const_wires, c)
    ripple_carry_add_wires(const_wires, b_wires, cin)
    _load_constant(None, const_wires, c)
