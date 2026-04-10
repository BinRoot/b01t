# b01t: Safe Quantum Programming

Memory-safe languages protect you from the dangers of `out-of-bounds access` and `null-pointer dereference`.

If you're reading this, you probably already know that quantum code has its own class of villains: `unexpected measurement`, `dirty ancillae`, `decoherence`, `unintended entanglement`, `bad uncomputation`, `gate noise`, and more.

b01t is Python DSL for safe quantum programming that compiles to Qiskit, where the type system enforces coherence and ancilla cleanliness.

Every well-typed safe b01t program denotes a unitary channel.
And under standard synthesis assumptions, b01t can express any unitary quantum circuit.

