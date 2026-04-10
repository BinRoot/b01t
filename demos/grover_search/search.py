"""Grover search: state prep + repeated oracle/diffusion + measurement.

The search itself is @adaptive (it measures). The oracle and diffusion
components are @coherent zoo modules.
"""

from b01t import QReg, adaptive, parametric, h, x, ccx, cz, mcx, z, measure_all, ancilla, compute, phase, uncompute, repeat


@parametric
def _grover_step_broad(sys: QReg):
    """One Grover iteration inlined for broad-IR use inside @adaptive."""
    # oracle
    with ancilla(1) as anc:
        compute(lambda: ccx(sys[0], sys[1], anc[0]))
        phase(lambda: z(anc[0]))
        uncompute()
    # diffusion
    for q in sys:
        h(q)
        x(q)
    with ancilla(1) as anc:
        compute(lambda: mcx(sys.wires()[:-1], anc[0]))
        phase(lambda: cz(anc[0], sys[-1]))
        uncompute()
    for q in sys:
        x(q)
        h(q)


@adaptive
def grover_search(sys: QReg):
    """Full Grover search: H layer, 2 iterations of oracle+diffusion, measure."""
    for q in sys:
        h(q)
    repeat(2, lambda: _grover_step_broad(sys))
    return measure_all(sys)
