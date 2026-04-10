"""Zero-state reflection S_0 = 2|0><0| - I.

Used by amplitude amplification and QAE as the "reflect about |0>"
step in the Grover iterate Q = A S_0 A† O_chi.

@coherent with proper ancilla discipline (MCZ via compute/phase/uncompute).
For 1-qubit registers, S_0 = Z (no ancilla needed).
"""

from b01t.core import QReg, coherent, cx, cz, mcx, x, z
from b01t.kit import ancilla, compute, phase, uncompute


@coherent
def zero_state_reflection(sys: QReg):
    """Reflect about |0...0>: S_0 = 2|0><0| - I."""
    n = len(sys)
    if n == 1:
        # S_0 on 1 qubit: Z gate (|0> -> |0>, |1> -> -|1>)
        z(sys[0])
        return

    for w in sys:
        x(w)
    if n == 2:
        # 2 qubits: CZ directly, no ancilla needed
        cz(sys[0], sys[1])
    else:
        # 3+ qubits: MCZ via ancilla
        with ancilla(1) as anc:
            compute(lambda: mcx(sys.wires()[:-1], anc[0]))
            phase(lambda: cz(anc[0], sys[-1]))
            uncompute()
    for w in sys:
        x(w)
