## Hero Theorem

Quantum programs allocate temporary qubits called ancillae. An ancilla
starts in the zero state |0>, participates in the computation, and must
be returned to |0> before being discarded. If it is not returned
cleanly, discarding it (tracing it out) destroys coherence: the system
becomes mixed, and the program no longer implements a unitary channel.

Classical compilers cannot check this property. A quantum circuit that
looks correct gate-by-gate can silently produce a mixed channel because
an ancilla was left entangled with the system. The SWAP gate is a
concrete example: it is coherent and unitary, but if one of its two
qubits is an ancilla initialized to |0>, the SWAP moves dirty system
data into the ancilla register, violating the cleanliness invariant.
No amount of type-checking on individual gates catches this.

This DSL exists to make ancilla cleanliness a structural property of
the language, enforced at build time, and backed by a machine-checked
proof in Lean 4 that every well-formed program denotes a unitary channel.

The central result is:

> **Hero Theorem.** The set of channels denotable by safe programs equals
> the set of unitary channels. Soundness requires zero hypotheses.
> Completeness requires one hypothesis (Solovay-Kitaev or exact synthesis).

---

## What the language does

The language is a first-order quantum circuit DSL with an effect system
that separates coherent (measurement-free) programs from adaptive
(measurement-using) programs, and a structural ancilla discipline that
restricts how temporary qubits are used inside coherent programs.

A program in the safe fragment:

1. Takes named quantum registers as input.
2. Applies gates from a library of unitaries.
3. Composes sub-circuits sequentially or in parallel (tensor product).
4. Allocates and uses ancilla qubits through a disciplined protocol.
5. Produces an IR that compiles to executable quantum circuits (e.g., Qiskit).

The language guarantees: if a program type-checks as safe, its
denotation (the function it computes on density matrices) is a unitary
channel. This guarantee holds without any runtime checks, without
simulation, and without trusting the gate library beyond its unitarity.

---

## How the language looks

### Terms

The core AST is `QTerm n m`, mapping `n` input qubits to `m` output
qubits:

```
QTerm ::=
  | gate(n, g)               -- library gate g on n qubits
  | seq(e1, e2)              -- sequential composition: e2 after e1
  | par(e1, e2)              -- parallel (tensor) composition: e1 ⊗ e2
  | meas(i, e0, e1)          -- measure qubit i, branch on outcome
  | ancilla(k, body)         -- allocate k ancillae, run body, trace out
  | ident(n)                 -- identity on n qubits
```

### The safe fragment

A term is **safe** (`IsSafe`) if it satisfies these structural rules:

```
IsSafe ::=
  | gate                     -- any library gate
  | seq(e1, e2)              -- both sub-terms are safe
  | par(e1, e2)              -- both sub-terms are safe
  | ident                    -- identity
  | ancilla(a, body)         -- body is safe AND a is an AncBlock AND
                             --   a.toMat is unitary AND
                             --   body's denotation = a.toMat conjugation
```

The key restriction: `meas` is excluded (no measurement), and `ancilla`
is only allowed when the body's matrix factors through an `AncBlock`.

### AncBlock: the ancilla discipline

An `AncBlock n k` is a certificate that the body of an ancilla allocation
is ancilla-clean. It is an inductive type with two constructors:

```
AncBlock ::=
  | cpu(C, D, hC: IsPerm C, hD: IsDiag D)    -- single CPU block
  | seq(a1, a2)                                -- sequential composition
```

A **CPU block** is a matrix of the form `C† D C` where:
- `C` is a **permutation matrix**: unitary, and every entry is 0 or 1.
- `D` is a **diagonal matrix**: zero off the diagonal.

In circuit terms:
- `C` is a classical reversible circuit (built from X, CX, CCX, MCX gates).
- `D` is a diagonal phase circuit (built from Z, RZ, CZ, CCZ, S, T gates).
- `C†DC` = apply C, then D, then undo C.

This is the **compute / phase / uncompute** pattern:
- **compute**: a permutation (classical-reversible) circuit.
- **phase**: a diagonal circuit.
- **uncompute**: the inverse of the compute circuit (which equals C† since C is a permutation).

### Surface syntax (DSL)

In the Python DSL, the safe fragment looks like:

```python
@coherent
def my_oracle(sys: QReg):
    h(sys[0])
    with ancilla(1) as anc:
        compute(lambda: cx(sys[0], anc[0]))   # permutation gates only
        phase(lambda: z(anc[0]))               # diagonal gates only
        uncompute()                            # auto-generated inverse
    ry(0.5, sys[1])
```

The `@coherent` decorator enforces: no measurement, no classical branching.
The `with ancilla` block enforces: exactly one `compute`, one `phase`,
one `uncompute`, in that order. The compute block rejects non-permutation
gates. The phase block rejects non-diagonal gates. The uncompute is
auto-generated as the reverse of compute.

Gates outside ancilla blocks are unrestricted (any unitary).

---

## The proof architecture

### Definitions (QuantumDefs.lean)

| Name | Type | Meaning |
|------|------|---------|
| `Mat d` | `Matrix (Fin d) (Fin d) ℂ` | Complex d×d matrix |
| `IsUnitary U` | `U * U† = I ∧ U† * U = I` | Unitary matrix |
| `IsUnitaryChannel Φ` | `∃ U, IsUnitary U ∧ Φ ρ = U ρ U†` | Unitary channel |
| `embedAncilla n k ρ` | `Mat (2^(n+k))` | Embed ρ ⊗ \|0^k⟩⟨0^k\| |
| `traceOutLast n k M` | `Mat (2^n)` | Trace out last k qubits |
| `denoteAncilla n k Φ ρ` | `traceOutLast(Φ(embedAncilla ρ))` | Ancilla semantics |
| `IsAncillaClean n k V` | `V(i·2^k+c, j·2^k) = 0 when c≠0` | Row-clean condition |
| `systemBlock n k V` | `V(i·2^k, j·2^k)` | Extract system sub-matrix |

### Ancilla discipline (AncillaDiscipline.lean)

The proof shows that CPU blocks are ancilla-clean:

1. **`cpu_ancilla_clean`**: If C is a permutation and D is diagonal, then
   `C†DC` is row-clean (IsAncillaClean). Proof: the permutation C maps
   each basis vector to exactly one other basis vector (0-or-1 entries),
   and the diagonal D only scales. The row-clean condition says
   `(C†DC)(i·2^k+c, j·2^k) = 0` when `c ≠ 0`. The proof shows this by
   expanding the matrix product and using the permutation property to
   derive a contradiction: if both `C(x, row)` and `C(x, col)` are 1
   for the same x but row ≠ col, then the unitarity `C†C = I` is violated.

2. **`cpu_col_clean`**: Column-clean (`V(i·2^k, j·2^k+c) = 0` when `c≠0`)
   follows from row-clean of the transpose `C†D†C` (since D† is also diagonal).

3. **`seq_fully_clean`**: Fully clean (row + column) composes under
   matrix multiplication. Proof: decompose intermediate index s into
   system part (d=0) and non-system part (d≠0). If d=0, row-clean of V2
   kills the term. If d≠0, row-clean of V1 kills it.

4. **`ancBlock_sound`**: Every `AncBlock` is ancilla-clean, by structural
   induction: cpu case uses `cpu_fully_clean`, seq case uses `seq_fully_clean`.

### The bridge (AncBridge.lean)

**`ancBridge`**: If V is unitary and ancilla-clean, then:
```
denoteAncilla n k (λ σ. V σ V†) ρ = systemBlock(V) * ρ * systemBlock(V)†
```

Proof: entry-wise matrix computation. The partial trace sums over the
ancilla index c. The clean condition collapses this sum to the single
term c=0 (all other terms vanish). What remains is exactly the system
block conjugation.

### Soundness (SafeComplete.lean)

**`safe_sound`**: Every safe term denotes a unitary channel.

Proof by structural induction on `IsSafe`:
- **gate**: library gates are unitary by assumption (`lib.unitary`).
- **seq**: sequential composition of unitary channels is unitary.
- **par**: tensor product of unitary channels is unitary. Uses the
  identity `tensorMap(U1·U1†, U2·U2†) = (U1⊗U2)·(U1⊗U2)†` proved in
  ParUnitary.lean, plus Kronecker and submatrix preserve unitarity.
- **ident**: identity is trivially unitary.
- **ancilla**: chains `ancBlock_sound` → `ancBridge` → `systemBlock_isometric`
  → `isometric_of_square_is_unitary`. Every step is fully proved.

**Zero hypotheses remain for soundness.**

### Completeness (ExactSynthesis.lean)

**`hero_theorem_exact`**: `DenSafe(n) = UnitarySet(n)`.

The completeness direction requires one hypothesis:

```
ExactSynthesis(lib) :=
  ∀ n U, IsUnitary U → ∃ e, IsSafe(e) ∧ denote(e) = (λ ρ. U ρ U†)
```

This says: every unitary can be exactly synthesized as a safe term.

The proof structure for discharging this hypothesis is:
1. **Two-level decomposition**: any d×d unitary is a product of
   two-level unitaries (Givens rotations). [sorry in the formalization]
2. **Two-level compilation**: each two-level unitary compiles to a
   circuit of 1-qubit gates + CNOT. Proved via routing (Gray code) +
   adjacent compilation (ABC decomposition). [sorry for the two sub-lemmas]
3. **Circuit embedding**: the intermediate `Circ` type embeds into
   `QTerm` as safe terms (no ancilla blocks needed, since the
   completeness witness is system-only).
4. **Bridge**: `ExactlyUniversal(lib)` (all 1-qubit unitaries + CNOT)
   implies `ExactSynthesis(lib)`, assembling the pipeline.

The sorry'd lemmas are standard quantum compilation results
(Reck et al. 1994, Barenco et al. 1995). Everything else is proved.

### The SWAP counterexample (SwapCounterexample.lean)

SWAP is coherent and unitary but NOT ancilla-clean:
```
swapMat(1, 2) = 1, but IsAncillaClean requires swapMat(0·2+1, 1·2) = 0.
```

This proves that coherence + unitarity alone are insufficient. The
AncBlock discipline is necessary: it rejects SWAP-like patterns because
SWAP is not of the form C†DC with C a permutation and D diagonal.

---

## Gate classification

The DSL enforces two gate categories inside ancilla blocks:

### Compute gates (permutation / classical-reversible)

| Gate | Wires | Allowed in `compute()` |
|------|-------|------------------------|
| X | 1 | yes |
| CX (CNOT) | 2 | yes |
| CCX (Toffoli) | 3 | yes |
| MCX (multi-controlled X) | n+1 | yes |
| SWAP | 2 | yes |

These gates map computational basis states to computational basis states.
Their matrix entries are all 0 or 1. They are the `IsPerm` matrices in
the proof.

### Phase gates (diagonal)

| Gate | Wires | Allowed in `phase()` |
|------|-------|----------------------|
| Z | 1 | yes |
| S, S† | 1 | yes |
| T, T† | 1 | yes |
| RZ(θ) | 1 | yes |
| CZ | 2 | yes |
| CCZ | 3 | yes |
| MCZ | n+1 | yes |

These gates only modify the phase of basis states, never the amplitude
structure. Their matrices are diagonal. They are the `IsDiag` matrices
in the proof.

### Unrestricted gates (outside ancilla blocks)

| Gate | Wires | Allowed in plain `@coherent` code |
|------|-------|----------------------------------|
| H, RY, RX, CRY, CRZ, ... | any | yes |

Any unitary gate is allowed outside ancilla blocks. These gates can
create superpositions, entangle qubits, and perform arbitrary rotations.
They correspond to `gate` terms in `IsSafe`, which are unconditionally safe.

---

## How to implement the DSL

### Step 1: Core types

Define `Wire`, `QReg` (named quantum registers), and the IR op types:
- `GateOp(name, wires, params)` — a gate application
- `AncillaBlockOp(ancilla_reg, compute_ops, phase_ops, uncompute_ops)` — disciplined ancilla block
- `MeasureOp`, `MeasureAllOp` — measurement (adaptive only)
- `IfOp` — classical branching (adaptive only)
- `IRProgram(name, effect, regs, ops, is_safe)` — complete program

### Step 2: Effect system

Two effects: `COHERENT` and `ADAPTIVE`.
- `@coherent` functions cannot contain measurement or classical branching.
- `@adaptive` functions can.
- A coherent function cannot call an adaptive function.

### Step 3: Build context and op routing

Maintain a context stack during program construction. When a gate is
emitted:
- If inside a `compute()` block: validate the gate is in `ALLOWED_COMPUTE`,
  append to the ancilla capture's compute list.
- If inside a `phase()` block: validate the gate is in `ALLOWED_PHASE`,
  append to the phase list.
- If inside an `ancilla` block but not in compute/phase: reject.
- Otherwise: append to the program's op list.

### Step 4: Ancilla discipline

The `with ancilla(k)` block:
1. Allocates a new register of k qubits.
2. Enters ancilla-capture mode.
3. Requires exactly one `compute(fn)` call, one `phase(fn)` call, one
   `uncompute()` call, in that order.
4. `compute(fn)`: executes fn, captures emitted GateOps. Validates all
   are in ALLOWED_COMPUTE. Validates no dirty-swap pattern (3 consecutive
   CX gates that form a SWAP).
5. `phase(fn)`: executes fn, captures emitted GateOps. Validates all are
   in ALLOWED_PHASE. Must follow compute.
6. `uncompute()`: auto-generates the inverse of the compute ops by
   reversing the list and applying the inverse of each gate. Must follow
   phase. Only one call allowed.
7. On block exit: packages everything into an `AncillaBlockOp`.

### Step 5: Adjoint

`adjoint(fn, *args)` emits the inverse of a coherent subroutine:
1. Builds the subroutine in a fresh context to capture its ops.
2. Reverses the op list and inverts each gate (using inverse rules).
3. Emits the inverted ops into the caller's context via `_append_op`
   (so ancilla-block restrictions are enforced).
4. Cannot be called inside an ancilla block.

Inverse rules:
- Self-inverse: X, H, Z, CX, CCX, CZ, CCZ, SWAP, MCX, MCZ
- Pairs: S ↔ S†, T ↔ T†
- Negation: RY(θ) → RY(-θ), RX(θ) → RX(-θ), RZ(θ) → RZ(-θ),
  CRY(θ) → CRY(-θ), CRZ(θ) → CRZ(-θ)

### Step 6: Safety checker

After building a program, run `is_safe_program(effect, ops)`:
1. Effect must be COHERENT.
2. Every op must be `GateOp` or `AncillaBlockOp` (no measure, no if).
3. For each `AncillaBlockOp`:
   - All compute_ops are GateOps with names in ALLOWED_COMPUTE.
   - All phase_ops are GateOps with names in ALLOWED_PHASE.
   - uncompute_ops is the exact reverse-inverse of compute_ops
     (same length, each gate is the inverse of the corresponding
     compute gate in reverse order).

### Step 7: Backend

Compile IR to a target circuit format (e.g., Qiskit):
- GateOps map directly to gate calls.
- AncillaBlockOps emit: compute_ops, then phase_ops, then uncompute_ops.
- Measurement ops emit measure instructions.

---

## How to verify correctness

An implementation is correct if it satisfies these testable properties:

### Property 1: Gate classification is exact

```
ALLOWED_COMPUTE = {x, cx, ccx, swap, mcx}
ALLOWED_PHASE   = {z, rz, cz, ccz, s, sdg, t, tdg, mcz}
```

Test: placing any ALLOWED_COMPUTE gate in a phase block must be rejected.
Placing any ALLOWED_PHASE gate in a compute block must be rejected.
Placing RY, H, CRY, or any rotation gate in either block must be rejected.

### Property 2: Ancilla block structure is enforced

- Multiple `compute()` calls in one block: rejected.
- Multiple `phase()` calls in one block: rejected.
- `phase()` before `compute()`: rejected.
- `uncompute()` before `phase()`: rejected.
- Missing `uncompute()` at block exit: rejected.
- Measurement inside an ancilla block: rejected.

### Property 3: Uncompute is the exact inverse

For every compute sequence, the auto-generated uncompute must satisfy:
```
for all i: uncompute[i] = inverse(compute[len-1-i])
```
where inverse is defined by the rules in Step 5.

Test: build a compute block with `[cx(a,b), ccx(a,b,c), x(d)]`,
verify uncompute is `[x(d), ccx(a,b,c), cx(a,b)]` (reversed, each
gate is self-inverse so identical).

Build a compute block with `[rz(0.5, q)]` — this must be REJECTED
since RZ is not in ALLOWED_COMPUTE.

### Property 4: SWAP rejection

A compute block containing three consecutive CX gates in the pattern
`cx(a,b), cx(b,a), cx(a,b)` must be rejected. This is the dirty-swap
pattern that the SWAP counterexample proves is unsafe.

### Property 5: Adjoint respects restrictions

`adjoint()` called inside an ancilla block must be rejected. The inverse
ops produced by adjoint must be routed through `_append_op` so that if
adjoint is somehow invoked in a compute or phase context, the gate
classification check still applies.

### Property 6: Safety checker is structural

`is_safe_program` must:
- Return False for any program containing MeasureOp or IfOp.
- Return False for any AncillaBlockOp whose compute_ops contain a
  non-ALLOWED_COMPUTE gate.
- Return False for any AncillaBlockOp whose phase_ops contain a
  non-ALLOWED_PHASE gate.
- Return False for any AncillaBlockOp whose uncompute_ops do not
  match the reverse-inverse of compute_ops.
- Return True for all programs that pass the above checks AND have
  effect COHERENT.

### Property 7: Denotational soundness (simulation test)

For small qubit counts (1-3 qubits), build safe programs, compile to
a matrix simulator, and verify:
- The output density matrix `Φ(ρ)` equals `U ρ U†` for some unitary U.
- The unitary U satisfies `U†U = I` and `UU† = I`.
- For programs with ancilla blocks: the ancilla qubits are in state |0>
  after the computation (verified by checking the partial trace).

### Property 8: SWAP counterexample passes at the matrix level

Build a 2-qubit SWAP circuit. Treat one qubit as system (n=1) and one
as ancilla (k=1). Compute the partial trace after applying SWAP to
`ρ ⊗ |0⟩⟨0|`. Verify that the result is NOT of the form `U ρ U†` for
any unitary U — i.e., the channel is not unitary. This confirms the
DSL's rejection of SWAP in compute blocks is necessary.

### Property 9: Completeness witness

For any 1-qubit unitary U, verify that a safe program exists whose
denotation is `ρ ↦ U ρ U†`. For multi-qubit unitaries, verify that
the gate library (all 1-qubit unitaries + CNOT) suffices to synthesize
any target unitary as a safe term (no ancilla blocks needed for the
completeness direction, since the witness is system-only).

---

## Correspondence between DSL and proof

| DSL construct | Lean type | Proof obligation |
|---------------|-----------|-----------------|
| `@coherent` | `IsCoh` | No measurement |
| `@coherent` + safe check | `IsSafe` | No measurement + AncBlock discipline |
| `compute()` body | `IsPerm C` | All gates are permutation matrices |
| `phase()` body | `IsDiag D` | All gates are diagonal matrices |
| `uncompute()` | `C†` | Inverse of compute (auto-generated) |
| `AncillaBlockOp` | `AncBlock.cpu C D hC hD` | C†DC is ancilla-clean |
| Sequential `AncillaBlockOp`s | `AncBlock.seq a b` | Clean blocks compose |
| `safe_sound` | `IsSafe → IsUnitaryChannel` | Main soundness theorem |
| `hero_theorem_exact` | `DenSafe = UnitarySet` | Exact set equality |

---

## What this manifest does NOT cover

- The approximate version of the hero theorem (uses `UniversalSafe` /
  Solovay-Kitaev instead of `ExactSynthesis`). Both are valid; the
  exact version is cleaner.
- The completeness proof internals (two-level decomposition, Gray code
  routing). These are standard quantum compilation and are sorry'd in
  the formalization.
- The older `IsCoh`-based soundness which requires `AncillaH` as an
  external hypothesis. The safe fragment supersedes it.
- Runtime simulation, error correction, or physical qubit mapping.
  This DSL operates at the logical circuit level.
