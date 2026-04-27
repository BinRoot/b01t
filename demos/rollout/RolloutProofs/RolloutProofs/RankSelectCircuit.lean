import RolloutProofs.RankSelectCommunication
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Nat.Log
import Mathlib.Tactic

/-!
# Rank-Select: Circuit Middle Tier

Circuit middle tier of the three-tier rank-select hierarchy
(function-level / sequential-scan in `RankSelectCommunication.lean`,
circuit here, gate-count consequences in `RankSelectGateLowerBound.lean`).
Formalizes the circuit-to-protocol reduction: a partitioned reversible
circuit with `crossBits` single-bit cross moves induces a two-party
protocol whose transcript is a `List.Vector Bool crossBits`. Combined
with `rankSelectProto_transcript_bound`, this yields
`min(t, N - t) ≤ 2^crossBits`, i.e., `crossBits ≥ log₂ min(t, N - t)`.

## Model

A `PartCircuit` is a straight-line sequence of `Move`s on a joint state
`α × β` (Alice × Bob). Each move is one of:
- `aliceStep f` - Alice updates her state locally.
- `bobStep f` - Bob updates her state locally.
- `crossAB sg fa fb` - Alice sends 1 bit `sg a`; both update.
- `crossBA sg fa fb` - Bob sends 1 bit `sg b`; both update.

A fan-in-`κ` crossing gate decomposes to at most `2κ` single-bit cross
moves. The charge `crossBits` is the total number of cross moves; the
fan-in accounting `crossBits ≤ 2κ · (crossing gates)` is mechanical and
not formalized here.

-/
/-! ## 1. Moves and `runMoves` -/

inductive Move (α β : Type*) where
  | aliceStep : (α → α) → Move α β
  | bobStep : (β → β) → Move α β
  | crossAB : (α → Bool) → (α → Bool → α) → (β → Bool → β) → Move α β
  | crossBA : (β → Bool) → (α → Bool → α) → (β → Bool → β) → Move α β

def Move.isCross {α β : Type*} : Move α β → Bool
  | .aliceStep _ => false
  | .bobStep _ => false
  | .crossAB _ _ _ => true
  | .crossBA _ _ _ => true

def applyMove {α β : Type*} : Move α β → α × β → α × β
  | .aliceStep f, (a, b) => (f a, b)
  | .bobStep f, (a, b) => (a, f b)
  | .crossAB sg fa fb, (a, b) =>
      let bit := sg a; (fa a bit, fb b bit)
  | .crossBA sg fa fb, (a, b) =>
      let bit := sg b; (fa a bit, fb b bit)

def runMoves {α β : Type*} : List (Move α β) → α × β → α × β
  | [], s => s
  | m :: rest, s => runMoves rest (applyMove m s)

def crossBits {α β : Type*} : List (Move α β) → Nat
  | [] => 0
  | .aliceStep _ :: rest => crossBits rest
  | .bobStep _ :: rest => crossBits rest
  | .crossAB _ _ _ :: rest => crossBits rest + 1
  | .crossBA _ _ _ :: rest => crossBits rest + 1

/-! ## 2. Transcript Extraction -/

/-- The list of bits communicated during `runMoves`. -/
def transcriptOf {α β : Type*} :
    List (Move α β) → α × β → List Bool
  | [], _ => []
  | .aliceStep f :: rest, (a, b) => transcriptOf rest (f a, b)
  | .bobStep f :: rest, (a, b) => transcriptOf rest (a, f b)
  | .crossAB sg fa fb :: rest, (a, b) =>
      let bit := sg a
      bit :: transcriptOf rest (fa a bit, fb b bit)
  | .crossBA sg fa fb :: rest, (a, b) =>
      let bit := sg b
      bit :: transcriptOf rest (fa a bit, fb b bit)

lemma transcriptOf_length {α β : Type*}
    (moves : List (Move α β)) (s : α × β) :
    (transcriptOf moves s).length = crossBits moves := by
  induction moves generalizing s with
  | nil => simp [transcriptOf, crossBits]
  | cons m rest ih =>
    obtain ⟨a, b⟩ := s
    cases m with
    | aliceStep f =>
        simp only [transcriptOf, crossBits]
        exact ih _
    | bobStep f =>
        simp only [transcriptOf, crossBits]
        exact ih _
    | crossAB sg fa fb =>
        simp only [transcriptOf, crossBits, List.length_cons]
        rw [ih _]
    | crossBA sg fa fb =>
        simp only [transcriptOf, crossBits, List.length_cons]
        rw [ih _]

/-! ## 3. Bob's Simulator -/

/-- Bob's reconstruction of his final β from his initial β and the
    transcript. Does not depend on α. -/
def bobSim {α β : Type*} :
    List (Move α β) → β → List Bool → β
  | [], b, _ => b
  | .aliceStep _ :: rest, b, bits => bobSim rest b bits
  | .bobStep f :: rest, b, bits => bobSim rest (f b) bits
  | .crossAB _ _ fb :: rest, b, bit :: bits =>
      bobSim rest (fb b bit) bits
  | .crossAB _ _ fb :: rest, b, [] =>
      bobSim rest (fb b false) []
  | .crossBA _ _ fb :: rest, b, bit :: bits =>
      bobSim rest (fb b bit) bits
  | .crossBA _ _ fb :: rest, b, [] =>
      bobSim rest (fb b false) []

/-- On the true transcript Bob recovers the true final β. -/
lemma bobSim_correct {α β : Type*}
    (moves : List (Move α β)) (a : α) (b : β) :
    bobSim moves b (transcriptOf moves (a, b)) =
      (runMoves moves (a, b)).2 := by
  induction moves generalizing a b with
  | nil => simp [bobSim, runMoves]
  | cons m rest ih =>
    cases m with
    | aliceStep f =>
        simp only [transcriptOf, bobSim, runMoves, applyMove]
        exact ih (f a) b
    | bobStep f =>
        simp only [transcriptOf, bobSim, runMoves, applyMove]
        exact ih a (f b)
    | crossAB sg fa fb =>
        simp only [transcriptOf, bobSim, runMoves, applyMove]
        exact ih (fa a (sg a)) (fb b (sg a))
    | crossBA sg fa fb =>
        simp only [transcriptOf, bobSim, runMoves, applyMove]
        exact ih (fa a (sg b)) (fb b (sg b))

/-! ## 4. Partitioned Circuit -/

structure PartCircuit (A B α β γ : Type*) where
  aliceInit : A → α
  bobInit : B → β
  moves : List (Move α β)
  readout : β → γ

def PartCircuit.compute {A B α β γ : Type*}
    (C : PartCircuit A B α β γ) (a : A) (b : B) : γ :=
  C.readout (runMoves C.moves (C.aliceInit a, C.bobInit b)).2

def PartCircuit.bits {A B α β γ : Type*}
    (C : PartCircuit A B α β γ) : Nat :=
  crossBits C.moves

/-! ## 5. Circuit → Protocol -/

/-- The transcript as a `List.Vector Bool C.bits`. -/
def PartCircuit.protoTranscript {A B α β γ : Type*}
    (C : PartCircuit A B α β γ) (a : A) (b : B) :
    List.Vector Bool C.bits :=
  ⟨transcriptOf C.moves (C.aliceInit a, C.bobInit b),
   transcriptOf_length C.moves _⟩

/-- Bob's output given his input and the transcript. -/
def PartCircuit.protoOutput {A B α β γ : Type*}
    (C : PartCircuit A B α β γ) (b : B)
    (v : List.Vector Bool C.bits) : γ :=
  C.readout (bobSim C.moves (C.bobInit b) v.toList)

/-- **Circuit-to-protocol reduction.** The induced protocol on
    transcript type `List.Vector Bool C.bits` computes `C.compute`. -/
theorem PartCircuit.protoOutput_transcript {A B α β γ : Type*}
    (C : PartCircuit A B α β γ) (a : A) (b : B) :
    C.protoOutput b (C.protoTranscript a b) = C.compute a b := by
  unfold PartCircuit.protoOutput PartCircuit.protoTranscript
      PartCircuit.compute
  change C.readout (bobSim C.moves (C.bobInit b)
      (transcriptOf C.moves (C.aliceInit a, C.bobInit b))) = _
  rw [bobSim_correct]

def PartCircuit.toProto {A B α β γ : Type*}
    (C : PartCircuit A B α β γ) :
    TwoParty A B γ (List.Vector Bool C.bits) where
  transcript := C.protoTranscript
  output := C.protoOutput

theorem PartCircuit.toProto_computes {A B α β γ : Type*}
    (C : PartCircuit A B α β γ) : C.toProto.Computes C.compute :=
  fun a b => C.protoOutput_transcript a b

/-! ## 6. Rank-Select Circuit -/

/-- A partitioned reversible circuit computing `rankSelect` at split `t`.
    Alice's input: `Fin t → Bool` (prefix). Bob's input:
    `(Fin (N - t) → Bool) × Nat` (suffix + rank). -/
structure RankSelectCircuit (N : Nat) where
  α : Type
  β : Type
  t : Nat
  ht : t ≤ N
  circuit :
      PartCircuit (Fin t → Bool) ((Fin (N - t) → Bool) × Nat) α β Nat
  correct :
      ∀ pre suf r,
        circuit.compute pre (suf, r) = rankSelect (glue ht pre suf) r

def RankSelectCircuit.toRSP {N : Nat} (C : RankSelectCircuit N) :
    RankSelectProto (List.Vector Bool C.circuit.bits) N where
  t := C.t
  ht := C.ht
  transcript := fun pre suf r => C.circuit.protoTranscript pre (suf, r)
  output := fun suf r v => C.circuit.protoOutput (suf, r) v

theorem RankSelectCircuit.toRSP_correct {N : Nat}
    (C : RankSelectCircuit N) : C.toRSP.Correct := by
  intro pre suf
  change C.circuit.protoOutput (suf, C.t - 1)
      (C.circuit.protoTranscript pre (suf, C.t - 1))
      = rankSelect (glue C.ht pre suf) (C.t - 1)
  rw [C.circuit.protoOutput_transcript]
  exact C.correct pre suf (C.t - 1)

/-! ## 7. Bits Lower Bound -/

/-- **Circuit communication lower bound.** Any partitioned reversible
    circuit computing rank-select at split `t` has `crossBits` ≥
    `log₂ min(t, N - t)`, in the form `min(t, N - t) ≤ 2^crossBits`. -/
theorem rankSelectCircuit_bits_bound {N : Nat}
    (C : RankSelectCircuit N) :
    min C.t (N - C.t) ≤ 2 ^ C.circuit.bits := by
  have h := rankSelectProto_transcript_bound C.toRSP C.toRSP_correct
  have h_card :
      Fintype.card (List.Vector Bool C.circuit.bits) =
        2 ^ C.circuit.bits := by
    rw [card_vector, Fintype.card_bool]
  change min C.toRSP.t (N - C.toRSP.t) ≤ _ at h
  change min C.t (N - C.t) ≤ _
  rw [← h_card]
  exact h

/-- Log-form statement: `log₂ min(t, N - t) ≤ crossBits`. -/
theorem rankSelectCircuit_bits_lower_bound {N : Nat}
    (C : RankSelectCircuit N) :
    Nat.log 2 (min C.t (N - C.t)) ≤ C.circuit.bits := by
  have h_bound : min C.t (N - C.t) ≤ 2 ^ C.circuit.bits :=
    rankSelectCircuit_bits_bound C
  have h_mono :
      Nat.log 2 (min C.t (N - C.t)) ≤ Nat.log 2 (2 ^ C.circuit.bits) :=
    Nat.log_mono_right h_bound
  rwa [Nat.log_pow (by norm_num : 1 < 2)] at h_mono

/-! ## 8. Fan-In Crossing-Gate Decomposition

A fan-in-`κ` crossing gate touches at most `κ` wires total, split as
`a` wires on Alice's side and `b` wires on Bob's side with `a + b ≤ κ`.
Standard decomposition into single-bit cross moves: Alice sends her
`a` bits to Bob (`a` `crossAB` moves), Bob applies the gate locally,
then Bob returns Alice's `a` updated bits (`a` `crossBA` moves).
Total cross moves per gate: `2 * a ≤ 2 * κ`.

`FanInGate α β κ` packages a move list with a proof
`crossBits moves ≤ 2 * κ`, certifying that one fan-in-`κ` gate has
been validly decomposed. A `FanInCircuit` is a list of such gates.
The theorem `expand_crossBits_le` shows the expansion yields at most
`2 * κ * G` cross moves, formalizing the fan-in accounting
`bits ≤ 2κ · (crossing gates)` that `CircuitWithCuts.bits_le`
(in `RankSelectGateLowerBound.lean`) takes as a structure field.
-/

/-- Append-additivity of `crossBits`. -/
@[simp] lemma crossBits_append {α β : Type*}
    (xs ys : List (Move α β)) :
    crossBits (xs ++ ys) = crossBits xs + crossBits ys := by
  induction xs with
  | nil => simp [crossBits]
  | cons m rest ih =>
    cases m with
    | aliceStep _ =>
        change crossBits (rest ++ ys) = crossBits rest + crossBits ys
        exact ih
    | bobStep _ =>
        change crossBits (rest ++ ys) = crossBits rest + crossBits ys
        exact ih
    | crossAB _ _ _ =>
        change crossBits (rest ++ ys) + 1 = crossBits rest + 1 + crossBits ys
        omega
    | crossBA _ _ _ =>
        change crossBits (rest ++ ys) + 1 = crossBits rest + 1 + crossBits ys
        omega

/-- One fan-in-`κ` crossing gate, certified to decompose into at most
    `2 * κ` single-bit cross moves. The `moves` list is the
    decomposition; `bits_bound` is the per-gate cost certificate. -/
structure FanInGate (α β : Type*) (κ : Nat) where
  moves : List (Move α β)
  bits_bound : crossBits moves ≤ 2 * κ

/-- A circuit assembled from fan-in-`κ` gates, run in order. -/
abbrev FanInCircuit (α β : Type*) (κ : Nat) : Type _ :=
  List (FanInGate α β κ)

namespace FanInCircuit

variable {α β : Type*} {κ : Nat}

/-- Concatenate every gate's decomposition in order. -/
def expand : FanInCircuit α β κ → List (Move α β)
  | [] => []
  | g :: rest => g.moves ++ expand rest

/-- **Fan-in accounting at the move-list level.** A circuit of `G`
    fan-in-`κ` crossing gates expands to a move list with at most
    `2 * κ * G` single-bit cross moves. -/
theorem expand_crossBits_le (C : FanInCircuit α β κ) :
    crossBits C.expand ≤ 2 * κ * C.length := by
  induction C with
  | nil => simp [expand, crossBits]
  | cons g rest ih =>
    change crossBits (g.moves ++ expand rest) ≤ 2 * κ * (rest.length + 1)
    rw [crossBits_append]
    calc crossBits g.moves + crossBits (expand rest)
        ≤ 2 * κ + 2 * κ * rest.length := Nat.add_le_add g.bits_bound ih
      _ = 2 * κ * (rest.length + 1) := by ring

end FanInCircuit

/-- **Constructive form of Corollary~3 (Crossing-gate bound).**
    If a `RankSelectCircuit` has its move list equal to the expansion
    of a fan-in-`κ` `FanInCircuit` of `G` gates, then
    `log₂ min(t, N - t) ≤ 2 * κ * G`. Combined with
    `rankSelectCircuit_bits_lower_bound`, this discharges the
    `bits_le` field of `CircuitWithCuts` constructively. -/
theorem rankSelectCircuit_fanIn_gates_bound {N κ : Nat}
    (RC : RankSelectCircuit N) (C : FanInCircuit RC.α RC.β κ)
    (h : RC.circuit.moves = C.expand) :
    Nat.log 2 (min RC.t (N - RC.t)) ≤ 2 * κ * C.length := by
  have h_bits : Nat.log 2 (min RC.t (N - RC.t)) ≤ RC.circuit.bits :=
    rankSelectCircuit_bits_lower_bound RC
  have h_eq : RC.circuit.bits = crossBits C.expand := by
    unfold PartCircuit.bits
    rw [h]
  rw [h_eq] at h_bits
  exact le_trans h_bits (FanInCircuit.expand_crossBits_le C)

/-! ## 9. Summary

### What this file establishes (third tier of the hierarchy)

- `PartCircuit`: partitioned straight-line reversible circuit model.
  Moves are Alice-local, Bob-local, or single-bit cross moves.
- `bits C = crossBits C.moves`: total single-bit cross moves.
- `protoTranscript`/`protoOutput`: constructive reduction to a
  two-party protocol with transcript type `List.Vector Bool bits`.
  Correctness: `protoOutput_transcript`.
- `RankSelectCircuit`: a `PartCircuit` computing `rankSelect` on every
  input (`correct : ∀ pre suf r, compute pre (suf, r) = rankSelect …`).
- `toRSP`: induces a `RankSelectProto`, `toRSP_correct` verifies it.
- `rankSelectCircuit_bits_bound`: `min(t, N - t) ≤ 2^bits`.
- `rankSelectCircuit_bits_lower_bound`: `log₂ min(t, N - t) ≤ bits`.
- `FanInGate` / `FanInCircuit` / `expand_crossBits_le`: every
  fan-in-`κ` circuit of `G` gates expands to at most `2 * κ * G`
  cross bits, formalizing the per-gate accounting.
- `rankSelectCircuit_fanIn_gates_bound`: combining with the cut
  bound gives `log₂ min(t, N - t) ≤ 2 * κ * G`, the constructive
  form of the paper's Crossing-gate bound corollary.

### Three tiers

1. **Function-level** (`rankSelectProto_transcript_bound` in
   `RankSelectCommunication`): every correct rank-select protocol needs
   `≥ log₂ min(t, N - t)` bits.
2. **Circuit** (this file): every partitioned reversible circuit
   computing rank-select has `crossBits ≥ log₂ min(t, N - t)`.
3. **Sequential-scan** (`workspace_per_cut_bound` in
   `RankSelectCommunication`): every correct scan has per-cut workspace
   size `≥ min(t, N - t)`.
-/
