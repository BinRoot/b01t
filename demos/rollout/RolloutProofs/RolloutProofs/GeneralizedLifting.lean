import RolloutProofs.BanditCore

/-!
# Generalized Hardness Lifting

Extends the exact-invariance lifting of `ManyHardBoards.lean` to an
approximate-invariance setting, replacing the locality requirement with a
bounded-influence condition.

## Main results

- `peripheral_perturbation_bound`: the telescoping lemma - single-site influence
  bounds compose additively over multiple modified sites.
- `generalized_hardness_lifting`: if arm `i` has gap >= 3*eps on a witness and
  peripheral modifications shift arms by <= eps, arm `i` is eps-optimal everywhere.
- `hardness_from_bounded_influence`: end-to-end composition - from single-site
  influence bounds to eps-optimality on the entire peripheral family.
- `exact_invariance_from_generalized`: the local-dynamics case (delta = 0) derived
  as a corollary of the generalized theorem.

## Relation to `ManyHardBoards`

`ManyHardBoards.concrete_hardness_lifting` requires exact value invariance
(locality: delta = 0). This file requires only bounded influence
(|mu_j(c) - mu_j(c*)| <= eps), covering non-local dynamics where
the mixing time exceeds the horizon (H < tau_mix).

## Mixing-time dichotomy

The bounded-influence condition holds whenever H < tau_mix (slow mixing):
- **Subcritical cascades** (pd < 1): influence decays geometrically with distance.
- **Polynomial mixing** (tau_mix = Theta(N^alpha), H << tau_mix): bounded total
  peripheral influence.

It fails when H >> tau_mix (fast mixing): the perturbation washes out and no
witness with a controlled gap can be constructed.
-/

open Real Finset Bandit

noncomputable section

namespace GeneralizedLifting

variable {k : ℕ}

-- ════════════════════════════════════════════════════════════════
-- § 1: Definitions
-- ════════════════════════════════════════════════════════════════

/-- Arm `i` has gap ≥ Δ: it beats every other arm by at least Δ. -/
def HasGap (inst : BanditInstance k) (i : Fin k) (Δ : ℝ) : Prop :=
  ∀ j : Fin k, j ≠ i → inst.μ i - inst.μ j ≥ Δ

/-- Single-site influence: changing one site shifts arm values by at most
    `influence(site)`. This is the condition generalizing locality - it holds
    for any dynamics where a one-cell modification has bounded effect on
    expected rollout outcomes. -/
def SingleSiteInfluence
    {Site State : Type*}
    (mv : (Site → State) → BanditInstance k)
    (influence : Site → ℝ) : Prop :=
  ∀ (c₁ c₂ : Site → State) (s : Site),
    (∀ t, t ≠ s → c₁ t = c₂ t) →
    ∀ j : Fin k, |(mv c₁).μ j - (mv c₂).μ j| ≤ influence s

/-- Peripheral family: configurations agreeing with `cStar` outside `P`. -/
def peripheralFamily {Site State : Type*}
    (cStar : Site → State) (P : Finset Site) : Set (Site → State) :=
  { c | ∀ s, s ∉ P → c s = cStar s }

-- ════════════════════════════════════════════════════════════════
-- § 2: Telescoping bridge
-- ════════════════════════════════════════════════════════════════

/-- **Telescoping lemma.** If changing any single site shifts arm values by
    at most `influence(site)`, then modifying all sites in `P` shifts arm
    values by at most `∑_{s ∈ P} influence(s)`.

    Proof: induction on `P`. At each step, restore one site to `cStar`,
    apply the single-site bound, and combine via the triangle inequality
    for absolute value. -/
theorem peripheral_perturbation_bound
    {Site State : Type*}
    (mv : (Site → State) → BanditInstance k)
    (influence : Site → ℝ)
    (hsi : SingleSiteInfluence mv influence)
    (cStar : Site → State)
    (P : Finset Site)
    (c : Site → State)
    (hc : ∀ s, s ∉ P → c s = cStar s)
    (j : Fin k) :
    |(mv c).μ j - (mv cStar).μ j| ≤ P.sum influence := by
  classical
  revert j c
  induction P using Finset.induction_on with
  | empty =>
    intro c hc j
    have heq : c = cStar := funext (fun s => hc s (by simp))
    subst heq; simp
  | @insert a P' ha ih =>
    intro c hc j
    -- Restore site `a` to `cStar`; keep `c` elsewhere.
    let c' : Site → State := fun t => if t = a then cStar t else c t
    have hc' : ∀ s, s ∉ P' → c' s = cStar s := by
      intro s hs
      change (if s = a then cStar s else c s) = cStar s
      split_ifs with h
      · rfl
      · exact hc s (by rw [Finset.mem_insert]; exact fun h' => h'.elim h hs)
    have hdiff : ∀ t, t ≠ a → c t = c' t := by
      intro t ht; change c t = if t = a then cStar t else c t; rw [if_neg ht]
    have h_site := hsi c c' a hdiff j
    have h_ih := ih c' hc' j
    rw [Finset.sum_insert ha, abs_le]
    exact ⟨by linarith [(abs_le.mp h_site).1, (abs_le.mp h_ih).1],
           by linarith [(abs_le.mp h_site).2, (abs_le.mp h_ih).2]⟩

-- ════════════════════════════════════════════════════════════════
-- § 3: Gap arithmetic
-- ════════════════════════════════════════════════════════════════

/-- A non-negative gap implies ε-optimality for any ε ≥ 0. -/
theorem gap_implies_epsOptimal
    (inst : BanditInstance k) (i : Fin k) (Δ ε : ℝ)
    (hΔ : 0 ≤ Δ) (hε : 0 ≤ ε) (hgap : HasGap inst i Δ) :
    IsEpsOptimal inst ε i := by
  intro j
  by_cases h : j = i
  · rw [h]; linarith
  · linarith [hgap j h]

/-- Under δ-perturbation of each arm's mean, the gap shrinks by at most 2δ. -/
theorem gap_after_perturbation
    (inst₁ inst₂ : BanditInstance k) (i : Fin k) (Δ δ : ℝ)
    (hgap : HasGap inst₁ i Δ)
    (hshift : ∀ j : Fin k, |inst₂.μ j - inst₁.μ j| ≤ δ) :
    HasGap inst₂ i (Δ - 2 * δ) := by
  intro j hj
  linarith [hgap j hj, (abs_le.mp (hshift j)).2, (abs_le.mp (hshift i)).1]

-- ════════════════════════════════════════════════════════════════
-- § 4: Abstract lifting
-- ════════════════════════════════════════════════════════════════

/-- **Generalized hardness lifting.** Gap ≥ 3ε on the witness plus
    perturbation ≤ ε on the family implies ε-optimality everywhere. -/
theorem generalized_hardness_lifting
    {Config : Type*}
    (mv : Config → BanditInstance k)
    (cStar : Config) (family : Set Config)
    (eps : ℝ) (heps : 0 < eps)
    (i : Fin k)
    (hgap : HasGap (mv cStar) i (3 * eps))
    (hperturb : ∀ c ∈ family, ∀ j : Fin k,
      |(mv c).μ j - (mv cStar).μ j| ≤ eps) :
    ∀ c ∈ family, IsEpsOptimal (mv c) eps i := by
  intro c hc
  have hgap' := gap_after_perturbation (mv cStar) (mv c) i (3 * eps) eps
    hgap (hperturb c hc)
  have : 3 * eps - 2 * eps = eps := by ring
  rw [this] at hgap'
  exact gap_implies_epsOptimal (mv c) i eps eps (le_of_lt heps) (le_of_lt heps) hgap'

-- ════════════════════════════════════════════════════════════════
-- § 5: End-to-end composition
-- ════════════════════════════════════════════════════════════════

/-- **Hardness from bounded influence.** Composes the telescoping bridge (§2)
    with generalized lifting (§4): single-site influence bounds + gap on
    witness + peripheral inertness ⟹ ε-optimality on the entire family.

    This is the theorem that replaces locality with bounded influence.
    To apply it to a non-local dynamics, verify:
    1. `SingleSiteInfluence` for your move-value function,
    2. `HasGap` on a witness configuration,
    3. `P.sum influence ≤ eps` for a peripheral site set. -/
theorem hardness_from_bounded_influence
    {Site State : Type*}
    (mv : (Site → State) → BanditInstance k)
    (influence : Site → ℝ)
    (hsi : SingleSiteInfluence mv influence)
    (cStar : Site → State)
    (P : Finset Site) (eps : ℝ) (heps : 0 < eps)
    (hP : P.sum influence ≤ eps)
    (i : Fin k)
    (hgap : HasGap (mv cStar) i (3 * eps)) :
    ∀ c ∈ peripheralFamily cStar P,
      IsEpsOptimal (mv c) eps i := by
  apply generalized_hardness_lifting mv cStar _ eps heps i hgap
  intro c hc j
  exact le_trans (peripheral_perturbation_bound mv influence hsi cStar P c hc j) hP

-- ════════════════════════════════════════════════════════════════
-- § 6: Exact invariance as corollary
-- ════════════════════════════════════════════════════════════════

/-- The local-dynamics case derived from the generalized theorem.
    When `mv c = mv cStar` for all family members, the perturbation is
    identically zero, so only the gap hypothesis is needed.

    `ManyHardBoards.value_invariance_implies_hardness` requires only
    ε-optimality (not HasGap 3ε), so it is strictly weaker in its
    hypotheses for the exact-invariance case. This corollary records
    that the local case factors through the general framework. -/
theorem exact_invariance_from_generalized
    {Config : Type*}
    (mv : Config → BanditInstance k)
    (cStar : Config) (family : Set Config)
    (eps : ℝ) (heps : 0 < eps)
    (i : Fin k)
    (hgap : HasGap (mv cStar) i (3 * eps))
    (hinvar : ∀ c ∈ family, mv c = mv cStar) :
    ∀ c ∈ family, IsEpsOptimal (mv c) eps i := by
  apply generalized_hardness_lifting mv cStar _ eps heps i hgap
  intro c hc j
  rw [hinvar c hc, sub_self, abs_zero]
  exact le_of_lt heps

-- ════════════════════════════════════════════════════════════════
-- § 7: Family counting
-- ════════════════════════════════════════════════════════════════

/-- Construct a family member from a peripheral assignment:
    use the assignment on `P`, use `cStar` elsewhere. -/
def assignPeripheral {Site State : Type*} [DecidableEq Site]
    (cStar : Site → State) (P : Finset Site)
    (f : ∀ _ : ↥P, State) : Site → State :=
  fun s => if h : s ∈ P then f ⟨s, h⟩ else cStar s

/-- Every peripheral assignment lands in the family. -/
theorem assignPeripheral_mem {Site State : Type*} [DecidableEq Site]
    (cStar : Site → State) (P : Finset Site) (f : ∀ _ : ↥P, State) :
    assignPeripheral cStar P f ∈ peripheralFamily cStar P := by
  intro s hs; simp [assignPeripheral, hs]

/-- Distinct assignments produce distinct family members. -/
theorem assignPeripheral_injective {Site State : Type*} [DecidableEq Site]
    (cStar : Site → State) (P : Finset Site) :
    Function.Injective (assignPeripheral cStar P) := by
  intro f g h; funext ⟨s, hs⟩
  have key := congr_fun h s; simp only [assignPeripheral, hs, ↓reduceDIte] at key; exact key

/-- There exist `|State|^|P|` distinct family members: `assignPeripheral`
    injects `(↥P → State)` into the family. -/
theorem family_exponentially_many {Site State : Type*} [Fintype State]
    (cStar : Site → State) (P : Finset Site) :
    ∃ (S : Finset (Site → State)),
      (∀ c ∈ S, c ∈ peripheralFamily cStar P) ∧
      S.card = Fintype.card State ^ P.card := by
  classical
  refine ⟨Finset.univ.image (assignPeripheral cStar P), ?_, ?_⟩
  · intro c hc
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hc
    obtain ⟨f, rfl⟩ := hc
    exact assignPeripheral_mem cStar P f
  · rw [Finset.card_image_of_injective _ (assignPeripheral_injective cStar P),
        Finset.card_univ]
    simp

/-- With q ≥ 2 states per site, the family has ≥ 2^|P| distinct members. -/
theorem family_size_exponential {Site State : Type*} [Fintype State]
    (cStar : Site → State) (P : Finset Site)
    (hq : 2 ≤ Fintype.card State) :
    ∃ (S : Finset (Site → State)),
      (∀ c ∈ S, c ∈ peripheralFamily cStar P) ∧
      2 ^ P.card ≤ S.card := by
  obtain ⟨S, hS, hcard⟩ := family_exponentially_many cStar P
  exact ⟨S, hS, hcard ▸ Nat.pow_le_pow_left (by omega) P.card⟩

end GeneralizedLifting
