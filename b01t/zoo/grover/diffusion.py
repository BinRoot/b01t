"""Diffusion operator: zero-state reflection S_0 = 2|0><0| - I in H basis."""

from b01t.core import QReg, coherent, cz, h, mcx, x, z
from b01t.kit import ancilla, compute, phase, uncompute


@coherent
def diffusion_operator(sys: QReg):
    """Grover diffusion: H-X-MCZ-X-H on all qubits."""
    n = len(sys)
    for q in sys:
        h(q)
        x(q)
    if n == 1:
        z(sys[0])
    elif n == 2:
        cz(sys[0], sys[1])
    else:
        with ancilla(1) as anc:
            compute(lambda: mcx(sys.wires()[:-1], anc[0]))
            phase(lambda: cz(anc[0], sys[-1]))
            uncompute()
    for q in sys:
        x(q)
        h(q)
