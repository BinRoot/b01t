"""Amplitude amplification: generalized Grover search.

Given:
  A:     @coherent state-preparation operator (A|0> = |psi>)
  O_chi: @coherent phase oracle marking "good" states with -1 phase

One Grover iterate Q = -A S_0 A† O_chi, where S_0 = I - 2|0><0|.

After k iterations of Q applied to A|0>, the amplitude of good states
is amplified from sqrt(p) to ~sin((2k+1) arcsin(sqrt(p))).

All components are @coherent with proper ancilla discipline.
The global phase (-1) from -S_0 is irrelevant and dropped.
"""

from typing import Callable

from b01t.core import QReg, coherent
from b01t.kit import adjoint
from b01t.zoo.amplitude_amplification.diffusion import zero_state_reflection


def make_amplification_step(
    state_prep: Callable,
    oracle: Callable,
):
    """Return a @coherent single amplification iterate Q.

    Q|psi> = A S_0 A† O_chi |psi>

    Args:
        state_prep: @coherent function(sys: QReg) implementing A
        oracle:     @coherent function(sys: QReg) implementing O_chi
                    (must flip phase of good states)

    The returned function takes:
        sys: the quantum register that A and O_chi operate on
    """

    @coherent
    def amplification_step(sys: QReg):
        # Step 1: mark good states with phase flip
        oracle(sys)
        # Step 2: diffusion about A|0> = A S_0 A†
        adjoint(state_prep, sys)
        zero_state_reflection(sys)
        state_prep(sys)

    return amplification_step


def make_amplitude_amplifier(
    state_prep: Callable,
    oracle: Callable,
    num_iterations: int,
):
    """Return a @coherent amplitude amplification circuit.

    Applies A (state prep) followed by num_iterations Grover iterates.

    Args:
        state_prep:     @coherent function(sys) implementing A
        oracle:         @coherent function(sys) implementing O_chi
        num_iterations: number of Q iterations (typically ~pi/4 * sqrt(N/M))

    The returned function takes:
        sys: quantum register (starts at |0...0>)
    """
    step = make_amplification_step(state_prep, oracle)

    @coherent
    def amplifier(sys: QReg):
        # Initial state preparation: A|0>
        state_prep(sys)
        # Amplify
        for _ in range(num_iterations):
            step(sys)

    return amplifier
