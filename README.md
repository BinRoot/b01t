# b01t: Safe Quantum Programming

Quantum code has its own class of bugs: dirty ancillae, bad uncomputation, silent decoherence. These pass type checks and compile fine in every existing framework. You only discover them by simulating the density matrix.

b01t is a Python DSL that catches these at build time. Every well-typed safe program is a proven unitary channel (the Hero Theorem, machine-checked in Lean 4).

## Example

A phase oracle in six lines:

```python
@coherent
def oracle(sys: QReg):
    with ancilla(1) as anc:
        compute(lambda: cx(sys[0], anc[0]))
        phase(lambda: z(anc[0]))
        uncompute()
```

The `compute` block copies system information into the ancilla using only classical-reversible gates. The `phase` block applies a diagonal rotation. The `uncompute` auto-generates the inverse. b01t proves at build time that the ancilla returns to |0> and the whole program is a unitary channel.

Now the mistake every quantum programmer makes at least once:

```python
@coherent
def broken(sys: QReg):
    with ancilla(1) as anc:
        compute(lambda: h(anc[0]))  # "just put it in superposition"
        phase(lambda: z(anc[0]))
        uncompute()

# DSLValidationError: gate 'h' is not allowed in compute blocks
```

Qiskit, Cirq, and Q# all accept this. It compiles, it runs, it looks fine. But since H is not a permutation gate, it creates superposition, which means the ancilla can end up entangled with the system after "uncomputation." The program silently becomes a mixed channel instead of a unitary.

b01t rejects it: compute blocks allow only permutation gates (X, CX, CCX, MCX), phase blocks allow only diagonal gates (Z, S, T, CZ, CCZ, MCZ). If your program passes these rules, it is a unitary channel. 

## Install

```bash
pip install b01t-lang
```

## Quick Start

```python
from b01t import coherent, ancilla, compute, phase, uncompute, cx, z
from b01t import lower_exact_program, QiskitBackend

@coherent
def oracle(sys):
    with ancilla(1) as anc:
        compute(lambda: cx(sys[0], anc[0]))
        phase(lambda: z(anc[0]))
        uncompute()

prog = oracle.build_exact(("sys", 1))
print(prog.certification)  # safe

qc = QiskitBackend().emit(lower_exact_program(prog))
print(qc)
#                      
#  sys:  ──■─────────■──
#        ┌─┴─┐┌───┐┌─┴─┐
# anc0:  ┤ X ├┤ Z ├┤ X ├
#        └───┘└───┘└───┘
```

## Development

```bash
uv sync
uv run pytest
```
