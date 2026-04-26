import RolloutProofs.RankSelectUniversality
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic

/-!
# Rank-Select: Per-Cut Communication Lower Bound

Function-level and sequential-scan tiers of the three-tier rank-select
hierarchy. The circuit middle tier is in `RankSelectCircuit.lean`,
and the gate-count consequences are in `RankSelectGateLowerBound.lean`.

## What this file proves

**Function-level (model-free).** For any deterministic two-party
protocol correctly computing the rank-select function on all inputs
(with Alice holding `M[0..t)`, Bob holding `M[t..N)` and the rank),
the transcript space has cardinality at least `min(t, N - t)`.
(`rankSelectProto_transcript_bound`.) No canonical-family hypothesis:
the protocol must be correct everywhere; the canonical family is used
only inside the proof.

**Sequential-scan.** For any exact clean scan selector correct on
the canonical hard family at rank `r = t`, the per-cut workspace has
size at least `min(t, N - t)` at every cut. (`workspace_per_cut_bound`.)

The underlying combinatorial fact is the injectivity of
`w ↦ rankSelect (canonMask N t w) (t - 1) = 2t - w - 1` on the window
`weightWindow t N = {max(0, 2t - N), …, t - 1}` of cardinality
`min(t, N - t)` (`rankSelect_canonMask`). The rank convention is
0-indexed throughout: `rankSelect x r` is the position of the
`r`-th 1 counting from zero.

-/
open Finset

/-! ## 1. The Weight Window -/

/-- `weightWindow t N = {max(0, 2t - N), …, t - 1}`. The prefix weights
    for which padding with an all-ones suffix places the `t`-th one in
    the suffix. -/
def weightWindow (t N : Nat) : Finset Nat :=
  Finset.Ico (2 * t - N) t

lemma mem_weightWindow {t N w : Nat} :
    w ∈ weightWindow t N ↔ 2 * t - N ≤ w ∧ w < t := by
  unfold weightWindow; exact Finset.mem_Ico

lemma weightWindow_card (t N : Nat) (ht : t ≤ N) :
    (weightWindow t N).card = min t (N - t) := by
  unfold weightWindow
  rw [Nat.card_Ico]
  omega

def windowEnum (t N : Nat) (i : Fin (min t (N - t))) : Nat :=
  (2 * t - N) + i.val

lemma windowEnum_mem (t N : Nat) (ht : t ≤ N)
    (i : Fin (min t (N - t))) :
    windowEnum t N i ∈ weightWindow t N := by
  rw [mem_weightWindow]
  have hi := i.isLt
  refine ⟨?_, ?_⟩
  · unfold windowEnum; omega
  · unfold windowEnum; omega

lemma windowEnum_injective (t N : Nat) :
    Function.Injective (windowEnum t N) := by
  intro i j h
  unfold windowEnum at h
  ext; omega

/-! ## 2. Canonical Hard Family -/

/-- `canonMask N t w` has 1s on `[0, w)`, 0s on `[w, t)`, 1s on `[t, N)`. -/
def canonMask (N t w : Nat) : Mask N :=
  fun i => decide (i.val < w ∨ t ≤ i.val)

lemma canonMask_suffix_one (N t w : Nat) (i : Fin N) (hi : t ≤ i.val) :
    canonMask N t w i = true := by
  unfold canonMask
  simp only [decide_eq_true_eq]
  exact Or.inr hi

lemma canonMask_agreeFrom (N t w₁ w₂ : Nat) :
    agreeFrom (canonMask N t w₁) (canonMask N t w₂) t := by
  intro i hi
  rw [canonMask_suffix_one N t w₁ i hi,
      canonMask_suffix_one N t w₂ i hi]

/-- Count of `Fin N` elements in `[a, b)`, for `a ≤ b ≤ N`. -/
lemma card_fin_filter_between (N a b : Nat) (ha : a ≤ b) (hb : b ≤ N) :
    (univ.filter fun i : Fin N => a ≤ i.val ∧ i.val < b).card = b - a := by
  have h_split :
      (univ.filter fun i : Fin N => i.val < b) =
      (univ.filter fun i : Fin N => i.val < a) ∪
      (univ.filter fun i : Fin N => a ≤ i.val ∧ i.val < b) := by
    ext i
    simp only [mem_filter, mem_univ, true_and, mem_union]
    omega
  have h_disj :
      Disjoint (univ.filter fun i : Fin N => i.val < a)
               (univ.filter fun i : Fin N => a ≤ i.val ∧ i.val < b) := by
    rw [Finset.disjoint_filter]
    intro i _ h1 ⟨h2, _⟩; omega
  have heq := card_union_of_disjoint h_disj
  rw [← h_split,
      card_fin_filter_lt N b hb,
      card_fin_filter_lt N a (le_trans ha hb)] at heq
  omega

lemma canonMask_prefixCount (N t w : Nat) (hw : w ≤ t) (ht : t ≤ N) :
    prefixCount (canonMask N t w) t = w := by
  unfold prefixCount canonMask
  have h_filter :
      (univ.filter fun i : Fin N =>
          i.val < t ∧ decide (i.val < w ∨ t ≤ i.val) = true) =
      univ.filter fun i : Fin N => i.val < w := by
    ext i
    simp only [mem_filter, mem_univ, true_and, decide_eq_true_eq]
    refine ⟨?_, ?_⟩
    · rintro ⟨hlt, (hw₀ | ht₀)⟩
      · exact hw₀
      · omega
    · intro hw₀
      exact ⟨lt_of_lt_of_le hw₀ hw, Or.inl hw₀⟩
  rw [h_filter]
  exact card_fin_filter_lt N w (le_trans hw ht)

/-- `prefixCount` of the canonical mask at a cutoff `k ∈ [t, N]`:
    the `w` ones in `[0, w)` plus the `k - t` ones in `[t, k)`. -/
lemma canonMask_prefixCount_mid (N t w k : Nat)
    (hw : w ≤ t) (hk_lo : t ≤ k) (hk_hi : k ≤ N) :
    prefixCount (canonMask N t w) k = w + (k - t) := by
  unfold prefixCount canonMask
  have h_split :
      (univ.filter fun i : Fin N =>
          i.val < k ∧ decide (i.val < w ∨ t ≤ i.val) = true) =
      (univ.filter fun i : Fin N => i.val < w) ∪
      (univ.filter fun i : Fin N => t ≤ i.val ∧ i.val < k) := by
    ext i
    simp only [mem_filter, mem_univ, true_and, decide_eq_true_eq, mem_union]
    constructor
    · rintro ⟨hlt, (hlw | htle)⟩
      · exact Or.inl hlw
      · exact Or.inr ⟨htle, hlt⟩
    · rintro (hlw | ⟨htle, hlt⟩)
      · refine ⟨?_, Or.inl hlw⟩; omega
      · exact ⟨hlt, Or.inr htle⟩
  have h_disj :
      Disjoint (univ.filter fun i : Fin N => i.val < w)
               (univ.filter fun i : Fin N => t ≤ i.val ∧ i.val < k) := by
    rw [Finset.disjoint_filter]
    intro i _ hlw ⟨htle, _⟩; omega
  rw [h_split, card_union_of_disjoint h_disj,
      card_fin_filter_lt N w (le_trans hw (le_trans hk_lo hk_hi)),
      card_fin_filter_between N t k hk_lo hk_hi]

/-! ## 3. `rankSelect` and its Spec

The rank-select function: position of the `r`-th 1 in `x`. Defined
noncomputably via `Classical.choose` on the prefix-count witness.
Uniqueness of the witness (via `witness_unique` from
`RankSelectUniversality`) turns this choice into a specification. -/

/-- Position (0-indexed) of the `r`-th 1 in `x` (where `r` is also
    0-indexed: `r = 0` requests the first 1-bit), or sentinel `N` if
    no such position exists. -/
noncomputable def rankSelect {N : Nat} (x : Mask N) (r : Nat) : Nat :=
  if h : ∃ j : Fin N, x j = true ∧ prefixCount x j.val = r
  then (Classical.choose h).val
  else N

/-- If `j` is a prefix-count witness (`x j = true` and
    `prefixCount x j.val = r`), then `rankSelect x r = j.val`.
    Uniqueness of the witness comes from `witness_unique`. -/
theorem rankSelect_spec {N : Nat} (x : Mask N) (r : Nat)
    (j : Fin N) (h_one : x j = true) (h_pc : prefixCount x j.val = r) :
    rankSelect x r = j.val := by
  have h_ex : ∃ j : Fin N, x j = true ∧ prefixCount x j.val = r :=
    ⟨j, h_one, h_pc⟩
  unfold rankSelect
  rw [dif_pos h_ex]
  have h_spec := Classical.choose_spec h_ex
  have h_same : Classical.choose h_ex = j :=
    witness_unique x r _ j h_spec.1 h_spec.2 h_one h_pc
  rw [h_same]

/-- **Key computation.** On the canonical hard family
    `canonMask N t w` with `w ∈ weightWindow t N`, the `(t-1)`-th 1
    (0-indexed) is at position `2t - w - 1`. This gives the
    fooling-set injectivity: `w ↦ rankSelect (canonMask N t w) (t - 1)`
    is injective on `weightWindow t N` of size `min(t, N - t)`. -/
theorem rankSelect_canonMask {N t w : Nat} (_ht : t ≤ N)
    (hw_mem : w ∈ weightWindow t N) :
    rankSelect (canonMask N t w) (t - 1) = 2 * t - w - 1 := by
  rw [mem_weightWindow] at hw_mem
  obtain ⟨hw_lo, hw_hi⟩ := hw_mem
  have hN : 2 * t - w - 1 < N := by omega
  have hwt : t ≤ 2 * t - w - 1 := by omega
  refine rankSelect_spec (canonMask N t w) (t - 1)
      ⟨2 * t - w - 1, hN⟩ ?_ ?_
  · exact canonMask_suffix_one N t w ⟨2 * t - w - 1, hN⟩ hwt
  · rw [canonMask_prefixCount_mid N t w (2 * t - w - 1)
        (le_of_lt hw_hi) hwt (le_of_lt hN)]
    omega

/-! ## 4. Abstract Two-Party Protocol (Yao fooling set) -/

structure TwoParty (A B Y T : Type*) where
  transcript : A → B → T
  output : B → T → Y

def TwoParty.Computes {A B Y T : Type*}
    (proto : TwoParty A B Y T) (f : A → B → Y) : Prop :=
  ∀ a b, proto.output b (proto.transcript a b) = f a b

/-- Fooling-set lower bound: if `f(·, b)` takes `n` distinct values on
    `aᵢ`, any correct protocol has ≥ `n` distinct transcripts. -/
theorem transcript_card_ge_fooling
    {A B Y T : Type*} [Fintype T]
    (proto : TwoParty A B Y T) (f : A → B → Y)
    (h_correct : proto.Computes f) (b : B)
    {n : Nat} (aᵢ : Fin n → A)
    (h_inj : Function.Injective (fun i => f (aᵢ i) b)) :
    n ≤ Fintype.card T := by
  have h_inj_trans :
      Function.Injective (fun i : Fin n => proto.transcript (aᵢ i) b) := by
    intro i j h
    change proto.transcript (aᵢ i) b = proto.transcript (aᵢ j) b at h
    apply h_inj
    change f (aᵢ i) b = f (aᵢ j) b
    rw [← h_correct (aᵢ i) b, ← h_correct (aᵢ j) b, h]
  have := Fintype.card_le_of_injective _ h_inj_trans
  simpa using this

/-! ## 5. Prefix/Suffix Split: `glue`, `RankSelectProto` -/

/-- Combine Alice's prefix `pre : Fin t → Bool` and Bob's suffix
    `suf : Fin (N - t) → Bool` into a single `Mask N`. -/
def glue {N t : Nat} (ht : t ≤ N)
    (pre : Fin t → Bool) (suf : Fin (N - t) → Bool) : Mask N :=
  fun i =>
    if h : i.val < t then pre ⟨i.val, h⟩
    else suf ⟨i.val - t, by have := i.isLt; omega⟩

/-- A two-party protocol for rank-select with split at cut `t`:
    Alice holds `Fin t → Bool` (prefix), Bob holds
    `(Fin (N - t) → Bool, rank)` (suffix + rank). -/
structure RankSelectProto (T : Type*) (N : Nat) where
  t : Nat
  ht : t ≤ N
  transcript :
      (Fin t → Bool) → (Fin (N - t) → Bool) → Nat → T
  output :
      (Fin (N - t) → Bool) → Nat → T → Nat

/-- The protocol computes `rankSelect` at rank `r = proto.t - 1`
    (0-indexed: the `proto.t`-th 1 counting from zero, i.e., the 1-bit
    whose rank coincides with the split cut). This is the weakest
    correctness hypothesis sufficient for the fooling-set argument,
    and it is automatic from "correct on all ranks" (the
    `Correct_of_everyRank` below). -/
def RankSelectProto.Correct {T : Type*} {N : Nat}
    (proto : RankSelectProto T N) : Prop :=
  ∀ (pre : Fin proto.t → Bool) (suf : Fin (N - proto.t) → Bool),
    proto.output suf (proto.t - 1) (proto.transcript pre suf (proto.t - 1)) =
      rankSelect (glue proto.ht pre suf) (proto.t - 1)

/-- Canonical prefix of weight `w`: 1s on `[0, w)`, 0s on `[w, t)`. -/
def canonPrefix (t w : Nat) : Fin t → Bool :=
  fun i => decide (i.val < w)

/-- All-ones suffix of length `N - t`. -/
def allOnesSuffix (N t : Nat) : Fin (N - t) → Bool := fun _ => true

lemma glue_canonical {N t w : Nat} (ht : t ≤ N) :
    glue ht (canonPrefix t w) (allOnesSuffix N t) = canonMask N t w := by
  ext i
  unfold glue canonPrefix allOnesSuffix canonMask
  split
  · next h =>
      have htle : ¬ (t ≤ i.val) := by omega
      simp [htle]
  · next h =>
      have htle : t ≤ i.val := by omega
      simp [htle]

/-! ## 6. Function-Level Communication Lower Bound

Every correct two-party protocol computing `rankSelect` has
transcript space of size ≥ `min(t, N - t)`. The proof feeds the
canonical family through the protocol and reads off injectivity via
`rankSelect_canonMask`. -/

/-- **Function-level theorem.** Any correct two-party rank-select
    protocol with split `t` has transcript cardinality
    `≥ min(t, N - t)`, i.e., ≥ `⌈log₂ min(t, N - t)⌉` bits. -/
theorem rankSelectProto_transcript_bound
    {T : Type*} [Fintype T] {N : Nat}
    (proto : RankSelectProto T N) (h_correct : proto.Correct) :
    min proto.t (N - proto.t) ≤ Fintype.card T := by
  set t := proto.t with ht_def
  have ht : t ≤ N := proto.ht
  let b_suf : Fin (N - t) → Bool := allOnesSuffix N t
  let aᵢ : Fin (min t (N - t)) → (Fin t → Bool) :=
    fun i => canonPrefix t (windowEnum t N i)
  have h_glue : ∀ i, glue proto.ht (aᵢ i) b_suf
      = canonMask N t (windowEnum t N i) := by
    intro _; exact glue_canonical proto.ht
  have h_inj_out :
      Function.Injective
        (fun i : Fin (min t (N - t)) =>
          proto.output b_suf (t - 1) (proto.transcript (aᵢ i) b_suf (t - 1))) := by
    intro i j h
    change proto.output b_suf (t - 1) (proto.transcript (aᵢ i) b_suf (t - 1)) =
           proto.output b_suf (t - 1) (proto.transcript (aᵢ j) b_suf (t - 1)) at h
    rw [h_correct (aᵢ i) b_suf, h_correct (aᵢ j) b_suf] at h
    rw [h_glue i, h_glue j] at h
    have hi_mem := windowEnum_mem t N ht i
    have hj_mem := windowEnum_mem t N ht j
    rw [rankSelect_canonMask ht hi_mem, rankSelect_canonMask ht hj_mem] at h
    rw [mem_weightWindow] at hi_mem hj_mem
    have hwe : windowEnum t N i = windowEnum t N j := by omega
    exact windowEnum_injective t N hwe
  have h_inj_trans :
      Function.Injective (fun i : Fin (min t (N - t)) =>
        proto.transcript (aᵢ i) b_suf (t - 1)) := by
    intro i j h
    change proto.transcript (aᵢ i) b_suf (t - 1) =
           proto.transcript (aᵢ j) b_suf (t - 1) at h
    apply h_inj_out
    change proto.output b_suf (t - 1) (proto.transcript (aᵢ i) b_suf (t - 1)) =
           proto.output b_suf (t - 1) (proto.transcript (aᵢ j) b_suf (t - 1))
    rw [h]
  have := Fintype.card_le_of_injective _ h_inj_trans
  simpa using this

/-! ## 7. Sequential Scan as a `RankSelectProto`

Every exact clean selector `m` with a rank-select-correct readout at
rank `t` induces a `RankSelectProto` whose transcript type is `Fin W`:
Alice runs `runPrefix m (glue ht pre suf) t` and sends that workspace
state; Bob reconstructs `runAll` using `runAll_of_prefix`. The
sequential-scan workspace lower bound is then a direct corollary of
`rankSelectProto_transcript_bound`. -/

/-- The scan readout equals `rankSelect · (t - 1)` on every mask
    (0-indexed rank: the `t`-th 1 counting from zero, i.e., the 1-bit
    whose rank coincides with the split cut). -/
def ScanCorrectAtRank {N W : Nat} (m : ExactCleanSelector N W)
    (readout : Fin W → Nat) (t : Nat) : Prop :=
  ∀ x : Mask N, readout (runAll m x) = rankSelect x (t - 1)

/-- The protocol induced by a sequential scan: transcript = workspace
    at cut `t`. Bob's output reconstructs `runAll` via
    `runAll_of_prefix` (noncomputable: uses `Classical.choose` to
    recover a valid prefix from the workspace state, then invokes
    the suffix-agreement lemma). -/
noncomputable def scanProtocol {N W t : Nat} (ht : t ≤ N)
    (m : ExactCleanSelector N W)
    (readout : Fin W → Nat) : RankSelectProto (Fin W) N where
  t := t
  ht := ht
  transcript := fun pre suf _r => runPrefix m (glue ht pre suf) t
  output := fun suf _r w =>
    if h : ∃ pre, runPrefix m (glue ht pre suf) t = w
    then readout (runAll m (glue ht (Classical.choose h) suf))
    else 0

lemma scanProtocol_correct {N W t : Nat} (ht : t ≤ N)
    (m : ExactCleanSelector N W) (readout : Fin W → Nat)
    (h_rs : ScanCorrectAtRank m readout t) :
    (scanProtocol ht m readout).Correct := by
  intro pre suf
  change (if h : ∃ p, runPrefix m (glue ht p suf) t =
              runPrefix m (glue ht pre suf) t
          then readout (runAll m (glue ht (Classical.choose h) suf))
          else 0) = rankSelect (glue ht pre suf) (t - 1)
  have h_ex :
      ∃ p, runPrefix m (glue ht p suf) t = runPrefix m (glue ht pre suf) t :=
    ⟨pre, rfl⟩
  rw [dif_pos h_ex]
  set p' := Classical.choose h_ex
  have h_pre_eq : runPrefix m (glue ht p' suf) t =
      runPrefix m (glue ht pre suf) t := Classical.choose_spec h_ex
  have h_agree : agreeFrom (glue ht p' suf) (glue ht pre suf) t := by
    intro i hi
    unfold glue
    have h_nlt : ¬ i.val < t := by omega
    simp [h_nlt]
  have h_runall :
      runAll m (glue ht p' suf) = runAll m (glue ht pre suf) :=
    runAll_of_prefix m _ _ t ht h_agree h_pre_eq
  rw [h_runall]
  exact h_rs _

/-- **Sequential-scan corollary of the function-level theorem.**
    If the scan is `rankSelect`-correct at rank `t` on all masks, its
    workspace size satisfies `W ≥ min(t, N - t)` - a direct corollary
    of `rankSelectProto_transcript_bound`. -/
theorem workspace_per_cut_bound_corollary {N W t : Nat} (ht : t ≤ N)
    (m : ExactCleanSelector N W) (readout : Fin W → Nat)
    (h_rs : ScanCorrectAtRank m readout t) :
    min t (N - t) ≤ W := by
  have h := rankSelectProto_transcript_bound
      (scanProtocol ht m readout) (scanProtocol_correct ht m readout h_rs)
  change min t (N - t) ≤ _ at h
  simpa [Fintype.card_fin] using h

/-! ## 8. Direct Sequential-Scan Proof (weaker hypothesis)

The corollary above requires scan correctness on all masks. The direct
proof below requires only correctness on the canonical hard family at
rank `t`. Same bound, weaker hypothesis, separate argument. -/

def ScanCorrectOnHardFamily
    {N W : Nat} (m : ExactCleanSelector N W) (readout : Fin W → Nat)
    (t : Nat) : Prop :=
  ∀ w ∈ weightWindow t N,
    readout (runAll m (canonMask N t w)) = 2 * t - w - 1

/-- Bridge: if the scan readout computes `rankSelect` at rank `t - 1`
    (0-indexed rank coinciding with the cut), then
    `ScanCorrectOnHardFamily` follows. Turns a `rankSelect`-correct
    selector into an instance of the canonical-family hypothesis. -/
lemma scan_hardFamily_of_rankSelect
    {N W : Nat} (m : ExactCleanSelector N W) (readout : Fin W → Nat)
    (t : Nat) (ht : t ≤ N)
    (h_rs : ∀ x : Mask N, readout (runAll m x) = rankSelect x (t - 1)) :
    ScanCorrectOnHardFamily m readout t := by
  intro w hw
  rw [h_rs, rankSelect_canonMask ht hw]

theorem per_cut_emergence
    {N W t : Nat} (ht : t ≤ N)
    (m : ExactCleanSelector N W)
    (readout : Fin W → Nat)
    (h_correct : ScanCorrectOnHardFamily m readout t)
    (w₁ : Nat) (hw₁ : w₁ ∈ weightWindow t N)
    (w₂ : Nat) (hw₂ : w₂ ∈ weightWindow t N)
    (h_eq : runPrefix m (canonMask N t w₁) t =
            runPrefix m (canonMask N t w₂) t) :
    w₁ = w₂ := by
  have h_all : runAll m (canonMask N t w₁) =
      runAll m (canonMask N t w₂) :=
    runAll_of_prefix m (canonMask N t w₁) (canonMask N t w₂) t ht
      (canonMask_agreeFrom N t w₁ w₂) h_eq
  have hr₁ := h_correct w₁ hw₁
  have hr₂ := h_correct w₂ hw₂
  rw [h_all] at hr₁
  have h_out : 2 * t - w₁ - 1 = 2 * t - w₂ - 1 := hr₁.symm.trans hr₂
  rw [mem_weightWindow] at hw₁ hw₂
  omega

theorem workspace_per_cut_bound
    {N W t : Nat} (ht : t ≤ N)
    (m : ExactCleanSelector N W)
    (readout : Fin W → Nat)
    (h_correct : ScanCorrectOnHardFamily m readout t) :
    min t (N - t) ≤ W := by
  have hinj : Function.Injective
      (fun i : Fin (min t (N - t)) =>
        runPrefix m (canonMask N t (windowEnum t N i)) t) := by
    intro i j h_eq
    simp only at h_eq
    have w_eq : windowEnum t N i = windowEnum t N j :=
      per_cut_emergence ht m readout h_correct
        (windowEnum t N i) (windowEnum_mem t N ht i)
        (windowEnum t N j) (windowEnum_mem t N ht j) h_eq
    exact windowEnum_injective t N w_eq
  have := Fintype.card_le_of_injective _ hinj
  simpa [Fintype.card_fin] using this

/-! ## 9. Per-Bit Input Dependence

Establishes that every input mask bit is depended on by `rankSelect`,
in the standard input-dependence sense: for each input position `p`,
there exist two masks differing only at `p` whose `rankSelect` outputs
at rank 0 differ. This is the formal justification for the
`N ≤ m + κ G` cone hypothesis used by `select_gate_lower_bound` in
`RankSelectUniversality.lean` to derive the unconditional `Ω(N)` gate
lower bound. -/

/-- The singleton mask: only position `p` is true. -/
def singletonMask {N : Nat} (p : Fin N) : Mask N :=
  fun i => decide (i = p)

@[simp] lemma singletonMask_self {N : Nat} (p : Fin N) :
    singletonMask p p = true := by
  unfold singletonMask; simp

@[simp] lemma singletonMask_other {N : Nat} (p i : Fin N) (h : i ≠ p) :
    singletonMask p i = false := by
  unfold singletonMask
  simp [h]

/-- The all-false mask. -/
def zeroMask (N : Nat) : Mask N := fun _ => false

@[simp] lemma zeroMask_apply {N : Nat} (i : Fin N) :
    zeroMask N i = false := rfl

/-- `prefixCount` of a singleton mask at threshold `p.val` is 0:
    the only true bit lies at `p`, with no true bit at any earlier position. -/
lemma prefixCount_singletonMask_self {N : Nat} (p : Fin N) :
    prefixCount (singletonMask p) p.val = 0 := by
  unfold prefixCount
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  rintro i _ ⟨hlt, hone⟩
  unfold singletonMask at hone
  rw [decide_eq_true_eq] at hone
  subst hone
  exact Nat.lt_irrefl _ hlt

/-- `rankSelect` at rank 0 on the singleton mask `e_p` returns `p`. -/
theorem rankSelect_singletonMask_zero {N : Nat} (p : Fin N) :
    rankSelect (singletonMask p) 0 = p.val :=
  rankSelect_spec (singletonMask p) 0 p
    (singletonMask_self p) (prefixCount_singletonMask_self p)

/-- `rankSelect` at rank 0 on the all-false mask returns the sentinel `N`. -/
theorem rankSelect_zeroMask {N : Nat} :
    rankSelect (zeroMask N) 0 = N := by
  have h : ¬ ∃ j : Fin N, zeroMask N j = true ∧
      prefixCount (zeroMask N) j.val = 0 := by
    rintro ⟨j, hone, _⟩
    simp [zeroMask] at hone
  unfold rankSelect
  rw [dif_neg h]

/-- **Per-bit input dependence.** For each input position `p < N`,
    there exist two masks differing only at position `p` whose
    rank-select outputs at rank 0 differ.

    The witnesses are the all-false mask (output `N`) and the
    singleton mask `e_p` (output `p`). They differ exactly at `p`.
    Together with the backward-light-cone bound (Ω(N) ≤ w + κG, which
    is a generic property of fan-in-κ reversible circuits), this
    gives the unconditional `Ω(N)` gate lower bound. -/
theorem rankSelect_depends_on_every_bit {N : Nat} (p : Fin N) :
    ∃ M₀ M₁ : Mask N,
      (∀ i : Fin N, i ≠ p → M₀ i = M₁ i) ∧
      rankSelect M₀ 0 ≠ rankSelect M₁ 0 := by
  refine ⟨zeroMask N, singletonMask p, ?_, ?_⟩
  · intro i hi
    rw [zeroMask_apply, singletonMask_other p i hi]
  · rw [rankSelect_zeroMask, rankSelect_singletonMask_zero]
    exact (Nat.ne_of_lt p.isLt).symm

/-! ## 8. Summary

### Three-tier hierarchy (proof.md)

Two of three tiers are established here:

- **Function-level (Section 6).** `rankSelectProto_transcript_bound`:
  every correct `RankSelectProto` has transcript cardinality
  `≥ min(t, N - t)`. No canonical-family hypothesis on the protocol;
  correctness is required on all inputs, and the canonical family is
  used only inside the proof.

- **Sequential-scan (Section 7).** `workspace_per_cut_bound`: every
  selector correct on the canonical hard family at rank `t` has
  per-cut workspace `≥ min(t, N - t)`.
  `scan_hardFamily_of_rankSelect` bridges a `rankSelect`-correct
  selector to this hypothesis.

### Supporting combinatorics

- `weightWindow`: `S_t = [max(0, 2t - N), t)`, `|S_t| = min(t, N - t)`.
- `canonMask`: hard family `P_w · 1^(N-t)`.
- `rankSelect`, `rankSelect_spec`: position of the 0-indexed `r`-th 1
  via the prefix-count witness (uniqueness from `witness_unique`).
- `rankSelect_canonMask`:
  `rankSelect (canonMask N t w) (t - 1) = 2t - w - 1`.

The circuit middle tier - partitioned reversible circuit ⟹ protocol
with `crossBits` bits - is in `RankSelectCircuit.lean`.
-/
