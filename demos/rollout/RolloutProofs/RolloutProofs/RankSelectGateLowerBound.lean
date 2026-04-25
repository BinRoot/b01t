import RolloutProofs.RankSelectCircuit
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Tactic

/-!
# Rank-Select: Bit-Level Gate Lower Bound (Summed-Cut)

Establishes an `Ω(Nw)` gate lower bound for the **bounded-span,
bounded-fan-in** circuit model. The per-cut bit bound
`rankSelectCircuit_bits_lower_bound` gives
`bits(t) ≥ log₂ min(t, N-t)` for every cut `t ∈ [1, N)`. Summing over
the window `t ∈ [N/4, N/2)` gives
`Σ log₂ min(t, N-t) ≥ (N/4)·(w - 2)` where `w = ⌊log₂ N⌋`.

The `CircuitWithCuts N fanin span` structure packages the cut-accounting
inequalities extracted from a single underlying gate list:

* `bits(t) ≤ 2·fanin·crossingsAt t` - a fan-in-`f` crossing gate
  decomposes to at most `2f` single-bit cross moves.
* `Σ_{t ∈ [1,N)} crossingsAt t ≤ span · nGates` - **each gate spans
  at most `span` cuts**. For geometrically 1D-local gates on wires
  contained in a contiguous block of width at most `κ`, one has
  `span ≤ κ - 1`. For all-to-all bounded-fan-in gates there is no
  non-trivial bound, so the hypothesis is not universally realizable;
  this is why the model qualifier `bounded-span` is part of the name.

Chaining the two inequalities with the per-cut log bound yields

  `(N/4)·(⌊log₂ N⌋ − 2) ≤ 2·fanin·span·nGates`,

i.e. `nGates = Ω(N·log₂ N / (fanin · span))`. For 1D-local circuits
with constant fan-in and constant span this is `Ω(Nw)`, matching the
`O(Nw)` upper bound from the sequential-scan construction.

This is `CircuitWithCuts.gate_lower_bound`. Producing a
`CircuitWithCuts` from an explicit gate list is mechanical for the
bounded-span model (decompose each gate into `≤ 2·fanin` cross moves
per cut it spans, and `span` counts its cuts-spanned). For arbitrary
bounded-fan-in circuits without a span bound, the summed-cut method
gives no better than the unconditional `Ω(N)` input-dependence bound
(`select_gate_lower_bound` in `RankSelectUniversality.lean`).

-/
open Finset

/-! ## 1. Log-divide Lemma -/

private lemma log_div_four_ge {N : Nat} (hN : 4 ≤ N) :
    Nat.log 2 N - 2 ≤ Nat.log 2 (N / 4) := by
  set w := Nat.log 2 N with hw_def
  have h4_eq : Nat.log 2 4 = 2 := by
    have : (4 : Nat) = 2 ^ 2 := by norm_num
    rw [this, Nat.log_pow (by norm_num : 1 < 2)]
  have hw : 2 ≤ w := by
    rw [← h4_eq]; exact Nat.log_mono_right hN
  have hN_ne : N ≠ 0 := by omega
  have h_pow : 2 ^ w ≤ N := Nat.pow_log_le_self 2 hN_ne
  have h_exp : 2 ^ (w - 2) * 4 = 2 ^ w := by
    have h4 : (4 : Nat) = 2 ^ 2 := by norm_num
    rw [h4, ← pow_add]
    congr 1; omega
  have h_div : 2 ^ (w - 2) ≤ N / 4 := by
    have h1 : 2 ^ (w - 2) = 2 ^ w / 4 := by
      rw [← h_exp, Nat.mul_div_cancel _ (by norm_num : (0 : Nat) < 4)]
    rw [h1]
    exact Nat.div_le_div_right h_pow
  have h_log_mono : Nat.log 2 (2 ^ (w - 2)) ≤ Nat.log 2 (N / 4) :=
    Nat.log_mono_right h_div
  rwa [Nat.log_pow (by norm_num : 1 < 2)] at h_log_mono

/-! ## 2. Window Log-Sum Bound -/

/-- For every `t ∈ [N/4, N/2)`, `min(t, N-t) = t ≥ N/4`. Summing gives
    `(N/4) · (⌊log₂ N⌋ - 2) ≤ Σ_t log₂ min(t, N-t)` on the window. -/
private lemma sum_log_min_window {N : Nat} (hN : 4 ≤ N) :
    (N / 4) * (Nat.log 2 N - 2) ≤
    ∑ t ∈ Ico (N / 4) (N / 2), Nat.log 2 (min t (N - t)) := by
  set L := Nat.log 2 N - 2 with hL
  have h_each : ∀ t ∈ Ico (N / 4) (N / 2),
      L ≤ Nat.log 2 (min t (N - t)) := by
    intro t ht
    rw [mem_Ico] at ht
    obtain ⟨h_lo, h_hi⟩ := ht
    have h_min : N / 4 ≤ min t (N - t) := by
      refine le_min h_lo ?_
      omega
    exact le_trans (log_div_four_ge hN) (Nat.log_mono_right h_min)
  have h_card_ge : N / 4 ≤ (Ico (N / 4) (N / 2)).card := by
    rw [Nat.card_Ico]
    omega
  have h_sum_const :
      ∑ _t ∈ Ico (N / 4) (N / 2), L = (Ico (N / 4) (N / 2)).card * L := by
    rw [sum_const, smul_eq_mul]
  calc (N / 4) * L
      ≤ (Ico (N / 4) (N / 2)).card * L := Nat.mul_le_mul_right L h_card_ge
    _ = ∑ _t ∈ Ico (N / 4) (N / 2), L := h_sum_const.symm
    _ ≤ ∑ t ∈ Ico (N / 4) (N / 2), Nat.log 2 (min t (N - t)) :=
        sum_le_sum h_each

/-! ## 3. Circuit-with-Cuts Structure

The structure is parameterized by **both** a fan-in bound `fanin`
(single-gate wire count) and a **span bound** `span` (maximum number
of mask cuts any single gate crosses). The two hypotheses
`bits_le` and `span_sum` are exactly the cut-accounting inequalities
under which the summed-cut argument goes through; neither follows
from `fanin` alone, which motivates the `bounded-span` name and the
explicit `span` parameter.
-/

/-- A cut-equipped bit-level reversible circuit on `N`-position
    masks, with fan-in bound `fanin` and per-gate cut-span bound
    `span`. For every cut `t ∈ [1, N)` it supplies a
    `RankSelectCircuit N` at that cut (derived from the same
    underlying gate pool of size `nGates`). `crossingsAt t` counts
    the gates whose support spans cut `t`; per-cut bits are bounded
    by `2·fanin·crossingsAt t` (fan-in-`f` cross-move decomposition),
    and total crossings by `span · nGates` (each gate's support spans
    at most `span` cuts).

    The `span` parameter makes the model's restriction explicit: for
    1D-local circuits with gate supports contained in a contiguous
    block of at most `κ` adjacent wires, `span = κ - 1` is the right
    bound. For all-to-all bounded-fan-in gates there is no non-trivial
    `span`, and the structure is not inhabited. -/
structure CircuitWithCuts (N fanin span : Nat) where
  nGates : Nat
  cutCircuit : ∀ t, 1 ≤ t → t < N → RankSelectCircuit N
  cutCircuit_t : ∀ t (h1 : 1 ≤ t) (h2 : t < N),
    (cutCircuit t h1 h2).t = t
  crossingsAt : Nat → Nat
  bits_le : ∀ t (h1 : 1 ≤ t) (h2 : t < N),
    (cutCircuit t h1 h2).circuit.bits ≤ 2 * fanin * crossingsAt t
  span_sum :
    ∑ t ∈ Ico 1 N, crossingsAt t ≤ span * nGates

namespace CircuitWithCuts

variable {N fanin span : Nat}

/-- Per-cut bits, extended by `0` outside `[1, N)`. -/
noncomputable def bitsAt (C : CircuitWithCuts N fanin span) (t : Nat) :
    Nat :=
  if h : 1 ≤ t ∧ t < N then (C.cutCircuit t h.1 h.2).circuit.bits else 0

lemma bitsAt_eq (C : CircuitWithCuts N fanin span) (t : Nat)
    (h1 : 1 ≤ t) (h2 : t < N) :
    C.bitsAt t = (C.cutCircuit t h1 h2).circuit.bits := by
  unfold bitsAt
  rw [dif_pos ⟨h1, h2⟩]

lemma log_min_le_bitsAt (C : CircuitWithCuts N fanin span) (t : Nat)
    (h1 : 1 ≤ t) (h2 : t < N) :
    Nat.log 2 (min t (N - t)) ≤ C.bitsAt t := by
  rw [bitsAt_eq C t h1 h2]
  have h := rankSelectCircuit_bits_lower_bound (C.cutCircuit t h1 h2)
  have ht_eq : (C.cutCircuit t h1 h2).t = t := C.cutCircuit_t t h1 h2
  have h_min :
      min (C.cutCircuit t h1 h2).t (N - (C.cutCircuit t h1 h2).t) =
      min t (N - t) := by rw [ht_eq]
  rw [h_min] at h
  exact h

lemma bitsAt_le (C : CircuitWithCuts N fanin span) (t : Nat)
    (h1 : 1 ≤ t) (h2 : t < N) :
    C.bitsAt t ≤ 2 * fanin * C.crossingsAt t := by
  rw [bitsAt_eq C t h1 h2]; exact C.bits_le t h1 h2

/-! ## 4. Main Theorem -/

/-- **Bounded-span, bounded-fan-in gate lower bound via summed cuts.**
    For a bit-level circuit on `N ≥ 4` mask positions with fan-in
    bound `fanin` and cut-span bound `span`, the gate count satisfies

      `(N/4) · (⌊log₂ N⌋ - 2) ≤ 2 · fanin · span · nGates`,

    i.e. `nGates = Ω(N · log₂ N / (fanin · span))`.

    For geometrically 1D-local gates with supports in a contiguous
    block of width ≤ `κ`, instantiating `fanin = κ` and `span = κ - 1`
    gives `Ω(Nw/κ²) = Ω(Nw)` for constant `κ`, matching the `O(Nw)`
    upper bound from `rank_select_gate_upper_bound_coarse`.

    This theorem does **not** establish an `Ω(Nw)` bound for unrestricted
    all-to-all bounded-fan-in circuits: a fan-in-2 gate on wires 1 and
    `N` spans all `N - 1` cuts, so no non-trivial `span` bound holds
    in that model. The unconditional bound for that case is the
    `Ω(N)` input-dependence bound of `select_gate_lower_bound`. -/
theorem gate_lower_bound (C : CircuitWithCuts N fanin span) (hN : 4 ≤ N) :
    (N / 4) * (Nat.log 2 N - 2) ≤ 2 * fanin * (span * C.nGates) := by
  have h_subset : Ico (N / 4) (N / 2) ⊆ Ico 1 N := by
    intro t ht
    rw [mem_Ico] at ht ⊢
    refine ⟨?_, ?_⟩
    · have : 1 ≤ N / 4 := by omega
      omega
    · omega
  calc (N / 4) * (Nat.log 2 N - 2)
      ≤ ∑ t ∈ Ico (N / 4) (N / 2), Nat.log 2 (min t (N - t)) :=
        sum_log_min_window hN
    _ ≤ ∑ t ∈ Ico (N / 4) (N / 2), C.bitsAt t := by
        apply sum_le_sum
        intro t ht
        rw [mem_Ico] at ht
        have h1 : 1 ≤ t := by omega
        have h2 : t < N := by omega
        exact C.log_min_le_bitsAt t h1 h2
    _ ≤ ∑ t ∈ Ico 1 N, C.bitsAt t := by
        apply sum_le_sum_of_subset_of_nonneg h_subset
        intros; exact Nat.zero_le _
    _ ≤ ∑ t ∈ Ico 1 N, 2 * fanin * C.crossingsAt t := by
        apply sum_le_sum
        intro t ht
        rw [mem_Ico] at ht
        exact C.bitsAt_le t ht.1 ht.2
    _ = 2 * fanin * ∑ t ∈ Ico 1 N, C.crossingsAt t := by
        rw [← mul_sum]
    _ ≤ 2 * fanin * (span * C.nGates) :=
        Nat.mul_le_mul_left (2 * fanin) C.span_sum

end CircuitWithCuts

/-! ## 5. Summary

The `CircuitWithCuts N fanin span` abstraction makes explicit that the
summed-cut argument depends on two independent parameters:

1. `fanin` - the single-gate wire count, entering via `bits(t) ≤
   2·fanin·crossingsAt t` (cross-move decomposition).
2. `span` - the maximum number of mask cuts any single gate crosses,
   entering via `Σ_t crossingsAt t ≤ span · nGates`.

The bound `(N/4)·(⌊log₂ N⌋ − 2) ≤ 2·fanin·span·nGates`, i.e.
`nGates = Ω(N log N / (fanin · span))`, is proved by summing
`log₂ min(t, N-t) ≤ bits(t)` over `t ∈ [N/4, N/2)` and chaining the
two inequalities above.

For 1D-local circuits (gates on a contiguous block of ≤ κ wires) the
natural instantiation is `fanin = κ`, `span = κ - 1`, giving `Ω(Nw)`
for constant `κ` - matching the `O(Nw)` upper bound of the
sequential-scan construction.

For all-to-all bounded-fan-in gates, no non-trivial `span` bound
holds (a fan-in-2 gate on wires `1` and `N` spans all `N - 1` cuts),
so this theorem does not apply. The unconditional lower bound in that
regime is `Ω(N)` (`select_gate_lower_bound` in
`RankSelectUniversality.lean`), not `Ω(Nw)`.
-/
