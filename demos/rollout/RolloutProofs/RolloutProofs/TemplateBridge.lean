import RolloutProofs.RolloutLowerBound
import RolloutProofs.GeneralizedLifting

/-!
# Template Bridge: Composing the Lower Bound with Hardness Lifting

The classical lower bound (`RolloutLowerBound.main_lower_bound`) proves
Omega(k/eps^2) for abstract bandit instances via Bretagnolle-Huber, which requires
base/alt instance pairs to **agree on all arms except the contender**.

The hardness lifting (`GeneralizedLifting.hardness_from_bounded_influence`)
preserves eps-optimality of a single arm across an exponential family, but does
not address the multi-instance agreement needed by Bretagnolle-Huber.

This file bridges the two by proving that **arm-disjoint locality** provides
exactly the inter-instance agreement the change-of-measure argument demands:

    arm-disjoint locality
      -> inter-instance agreement (S 2)
        -> per-arm KL bound via Bretagnolle-Huber (S 4)
          -> Omega(k/eps^2) total rollouts (S 5)
            -> lifted to |State|^|P| configurations (S 7-8)

## Main results

- `agreement_from_disjoint_support`: locality implies the `hagree` hypothesis of Bretagnolle-Huber.
- `peripheral_invariance`: peripheral family shares the move-value vector.
- `generalized_main_lower_bound`: Omega(k/eps^2) for arbitrary template instances.
- `composed_lower_bound`: end-to-end - disjoint support gives the lower bound.
- `lower_bound_on_exponential_family`: Omega(k/eps^2) on `|State|^|P|` configurations.

## Relation to existing files

- `RolloutLowerBound`: the per-arm information-theoretic bound
  (specialized to specific mean values 1/2, 1/2+4eps, 1/2+6eps).
- `GeneralizedLifting`: the family construction and counting.
- `ManyHardBoards`: the Sway-game instantiation (exact invariance).
- This file: the composition layer connecting all three.
-/

set_option linter.unusedVariables false
set_option linter.style.setOption false
set_option linter.flexible false
set_option linter.unusedFintypeInType false

open Real Finset Bandit GeneralizedLifting

noncomputable section

namespace TemplateBridge

variable {k : ℕ}

-- ════════════════════════════════════════════════════════════════
-- S 1: Arm-disjoint support
-- ════════════════════════════════════════════════════════════════

/-- Arm-disjoint support: arm i's mean depends only on sites in
    `support i`, and different arms have disjoint supports.

    In the Sway game: `support i` = N_H(firstMove i), the H-ball
    around the first move. Disjointness holds when first moves are
    spaced > 2H apart on the grid. -/
structure ArmDisjointSupport
    {Site State : Type*}
    (mv : (Site → State) → BanditInstance k)
    (support : Fin k → Finset Site) : Prop where
  /-- Arm i's mean depends only on sites in `support i`. -/
  arm_locality : ∀ (i : Fin k) (c₁ c₂ : Site → State),
    (∀ s, s ∈ support i → c₁ s = c₂ s) →
    (mv c₁).μ i = (mv c₂).μ i
  /-- Distinct arms have disjoint support regions. -/
  arm_disjoint : ∀ (i j : Fin k), i ≠ j →
    Disjoint (support i) (support j)

/-- Extensionality for BanditInstance (single-field structure). -/
private theorem bandit_ext {a b : BanditInstance k}
    (h : a.μ = b.μ) : a = b := by
  obtain ⟨_⟩ := a; obtain ⟨_⟩ := b; exact congrArg BanditInstance.mk h

-- ════════════════════════════════════════════════════════════════
-- S 2: Agreement from disjoint support
-- ════════════════════════════════════════════════════════════════

/-- **The bridge lemma.** Under arm-disjoint support, modifying only
    sites in `support j` preserves every other arm's mean.

    This provides the `hagree` condition required by
    `bretagnolle_huber_chain_rule` for the change-of-measure argument.

    Proof: for i != j, any site s in support i satisfies s not in support j
    (disjointness), so the modification at s is the identity. -/
theorem agreement_from_disjoint_support
    {Site State : Type*}
    (mv : (Site → State) → BanditInstance k)
    (support : Fin k → Finset Site)
    (hds : ArmDisjointSupport mv support)
    (c₀ c₁ : Site → State)
    (j : Fin k)
    (hmod : ∀ s, s ∉ support j → c₁ s = c₀ s)
    (i : Fin k) (hi : i ≠ j) :
    (mv c₀).μ i = (mv c₁).μ i :=
  (hds.arm_locality i c₁ c₀ (fun s hs =>
    hmod s (Finset.disjoint_left.mp (hds.arm_disjoint i j hi) hs))).symm

-- ════════════════════════════════════════════════════════════════
-- S 3: Peripheral invariance
-- ════════════════════════════════════════════════════════════════

/-- If the peripheral set P is disjoint from every arm's support,
    then all configurations in the peripheral family share the base's
    move-value vector.

    This derives the `hinvar` condition for lifting from
    `ArmDisjointSupport` and the geometric constraint that P lies
    outside all rollout regions. -/
theorem peripheral_invariance
    {Site State : Type*}
    (mv : (Site → State) → BanditInstance k)
    (support : Fin k → Finset Site)
    (hds : ArmDisjointSupport mv support)
    (base : Site → State) (P : Finset Site)
    (hP_disj : ∀ i : Fin k, Disjoint (support i) P)
    (c : Site → State) (hc : c ∈ peripheralFamily base P) :
    mv c = mv base :=
  bandit_ext (funext (fun i =>
    hds.arm_locality i c base (fun s hs =>
      hc s (Finset.disjoint_left.mp (hP_disj i) hs))))

-- ════════════════════════════════════════════════════════════════
-- S 4: Generalized per-arm bound
-- ════════════════════════════════════════════════════════════════

/-- **Generalized per-arm bound.** For any two instances that agree on
    all arms except j, with output-probability and KL conditions,
    arm j requires at least kl(1/3, 2/3) / C pulls under the base.

    Generalizes `SwayRollout.per_arm_bound` from the specific mean
    values (1/2, 1/2+6eps) to arbitrary instances with KL upper bound C. -/
theorem per_arm_bound_general
    (A : BanditAlgorithm k)
    (base_inst alt_inst : BanditInstance k) (j : Fin k)
    (hagree : ∀ i : Fin k, i ≠ j → base_inst.μ i = alt_inst.μ i)
    (hP0 : outputProb A base_inst j ≤ 1/3)
    (hP1 : 2/3 ≤ outputProb A alt_inst j)
    (hkl_pos : 0 < bernoulliKL (base_inst.μ j) (alt_inst.μ j))
    (C : ℝ) (hC : 0 < C)
    (hkl_ub : bernoulliKL (base_inst.μ j) (alt_inst.μ j) ≤ C) :
    bernoulliKL (1/3) (2/3) / C ≤ expectedPulls A base_inst j := by
  have hBH := bretagnolle_huber_chain_rule A base_inst alt_inst j
    hagree hP0 hP1 hkl_pos
  have hklBH_pos : 0 < bernoulliKL (1/3) (2/3) := by
    rw [SwayRollout.kl_one_third_two_thirds]; positivity
  calc bernoulliKL (1/3) (2/3) / C
      ≤ bernoulliKL (1/3) (2/3) / bernoulliKL (base_inst.μ j) (alt_inst.μ j) :=
        div_le_div_of_nonneg_left (le_of_lt hklBH_pos) hkl_pos hkl_ub
    _ ≤ expectedPulls A base_inst j := by rwa [div_le_iff₀ hkl_pos]

-- ════════════════════════════════════════════════════════════════
-- S 5: Generalized main lower bound
-- ════════════════════════════════════════════════════════════════

/-- **Generalized main lower bound.** Any algorithm correct on a
    base/alt template with uniform KL bound C requires
    (k-1) * kl(1/3, 2/3) / C total rollouts under the base.

    Generalizes `SwayRollout.main_lower_bound` from the specific
    (1/2, 1/2+4eps, 1/2+6eps) template to arbitrary instances.

    When C = 96 eps^2 (the Bernoulli KL bound from RolloutLowerBound),
    this recovers (k-1) * log 2 / (288 eps^2). -/
theorem generalized_main_lower_bound
    (k : ℕ) (hk : 2 ≤ k)
    (A : BanditAlgorithm k)
    (base_inst : BanditInstance k)
    (alt_inst : Fin k → BanditInstance k)
    (C : ℝ) (hC : 0 < C)
    (hagree : ∀ j : Fin k, j.val ≠ 0 → ∀ i : Fin k, i ≠ j →
      base_inst.μ i = (alt_inst j).μ i)
    (hP0 : ∀ j : Fin k, j.val ≠ 0 → outputProb A base_inst j ≤ 1/3)
    (hP1 : ∀ j : Fin k, j.val ≠ 0 → 2/3 ≤ outputProb A (alt_inst j) j)
    (hkl_pos : ∀ j : Fin k, j.val ≠ 0 →
      0 < bernoulliKL (base_inst.μ j) ((alt_inst j).μ j))
    (hkl_ub : ∀ j : Fin k, j.val ≠ 0 →
      bernoulliKL (base_inst.μ j) ((alt_inst j).μ j) ≤ C) :
    (↑(k - 1) : ℝ) * (bernoulliKL (1/3) (2/3) / C) ≤
      expectedTotal A base_inst := by
  set S := Finset.univ.erase (⟨0, by omega⟩ : Fin k)
  have hcard : S.card = k - 1 := by simp [S, card_erase_of_mem (mem_univ _)]
  have hper : ∀ j ∈ S, bernoulliKL (1/3) (2/3) / C ≤
      expectedPulls A base_inst j := by
    intro j hj; simp [S, mem_erase, Fin.ext_iff] at hj
    exact per_arm_bound_general A base_inst (alt_inst j) j
      (hagree j hj) (hP0 j hj) (hP1 j hj) (hkl_pos j hj) C hC (hkl_ub j hj)
  calc (↑(k-1) : ℝ) * (bernoulliKL (1/3) (2/3) / C)
      = S.card • (bernoulliKL (1/3) (2/3) / C) := by rw [hcard, nsmul_eq_mul]
    _ ≤ S.sum (fun j => expectedPulls A base_inst j) :=
        card_nsmul_le_sum _ _ _ hper
    _ ≤ univ.sum (fun j => expectedPulls A base_inst j) :=
        sum_le_sum_of_subset_of_nonneg (erase_subset _ _)
          (fun j _ _ => expectedPulls_nonneg A _ j)
    _ ≤ expectedTotal A base_inst := total_ge_sum_pulls A _

-- ════════════════════════════════════════════════════════════════
-- S 6: Composed lower bound
-- ════════════════════════════════════════════════════════════════

/-- **Composed lower bound.** End-to-end composition from game-level
    structure to information-theoretic bound:

      arm-disjoint support + template configurations -> Omega(k/eps^2)

    Takes game-level inputs (move-value function, support regions,
    base/alt configurations) and derives the lower bound by:
    1. Extracting inter-instance agreement from disjoint support (S 2)
    2. Applying the generalized main lower bound (S 5) -/
theorem composed_lower_bound
    {Site State : Type*}
    (mv : (Site → State) → BanditInstance k)
    (support : Fin k → Finset Site)
    (hds : ArmDisjointSupport mv support)
    (base : Site → State)
    (alt : Fin k → Site → State)
    (halt_mod : ∀ j : Fin k, j.val ≠ 0 →
      ∀ s, s ∉ support j → (alt j) s = base s)
    (A : BanditAlgorithm k) (hk : 2 ≤ k)
    (hP0 : ∀ j : Fin k, j.val ≠ 0 →
      outputProb A (mv base) j ≤ 1/3)
    (hP1 : ∀ j : Fin k, j.val ≠ 0 →
      2/3 ≤ outputProb A (mv (alt j)) j)
    (C : ℝ) (hC : 0 < C)
    (hkl_pos : ∀ j : Fin k, j.val ≠ 0 →
      0 < bernoulliKL ((mv base).μ j) ((mv (alt j)).μ j))
    (hkl_ub : ∀ j : Fin k, j.val ≠ 0 →
      bernoulliKL ((mv base).μ j) ((mv (alt j)).μ j) ≤ C) :
    (↑(k - 1) : ℝ) * (bernoulliKL (1/3) (2/3) / C) ≤
      expectedTotal A (mv base) :=
  generalized_main_lower_bound k hk A (mv base) (fun j => mv (alt j)) C hC
    (fun j hj i hi =>
      agreement_from_disjoint_support mv support hds base (alt j) j
        (halt_mod j hj) i hi)
    hP0 hP1 hkl_pos hkl_ub

-- ════════════════════════════════════════════════════════════════
-- S 7: Exact lifting
-- ════════════════════════════════════════════════════════════════

/-- A bandit algorithm interacts with the configuration only through
    the move-value vector. Configurations with identical vectors produce
    identical algorithm behavior, so any lower bound transfers. -/
theorem lower_bound_transfers
    {Config : Type*}
    (mv : Config → BanditInstance k)
    (A : BanditAlgorithm k)
    (base c : Config)
    (hinvar : mv c = mv base)
    (bound : ℝ)
    (hlb : bound ≤ expectedTotal A (mv base)) :
    bound ≤ expectedTotal A (mv c) := hinvar ▸ hlb

-- ════════════════════════════════════════════════════════════════
-- S 8: Exponential family
-- ════════════════════════════════════════════════════════════════

/-- **Full composition.** The Omega(k/eps^2) lower bound holds on
    |State|^|P| distinct configurations in the peripheral family.

    Composes four results:
    1. `composed_lower_bound` (S 6): Omega(k/eps^2) on the base
    2. `peripheral_invariance` (S 3): the family shares the base's
       move-value vector (because P is disjoint from all supports)
    3. `lower_bound_transfers` (S 7): identical vectors -> same bound
    4. `family_exponentially_many` (GeneralizedLifting): |State|^|P| members

    The result: the lower bound holds uniformly on an exponential set,
    not just on a single pathological configuration. -/
theorem lower_bound_on_exponential_family
    {Site State : Type*} [Fintype State]
    (mv : (Site → State) → BanditInstance k)
    (support : Fin k → Finset Site)
    (hds : ArmDisjointSupport mv support)
    -- Base and peripheral set
    (base : Site → State)
    (P : Finset Site)
    (hP_disj : ∀ i : Fin k, Disjoint (support i) P)
    -- Alt configurations (modify support j to boost arm j)
    (alt : Fin k → Site → State)
    (halt_mod : ∀ j : Fin k, j.val ≠ 0 →
      ∀ s, s ∉ support j → (alt j) s = base s)
    -- Algorithm and correctness
    (A : BanditAlgorithm k) (hk : 2 ≤ k)
    (hP0 : ∀ j : Fin k, j.val ≠ 0 →
      outputProb A (mv base) j ≤ 1/3)
    (hP1 : ∀ j : Fin k, j.val ≠ 0 →
      2/3 ≤ outputProb A (mv (alt j)) j)
    -- KL bounds
    (C : ℝ) (hC : 0 < C)
    (hkl_pos : ∀ j : Fin k, j.val ≠ 0 →
      0 < bernoulliKL ((mv base).μ j) ((mv (alt j)).μ j))
    (hkl_ub : ∀ j : Fin k, j.val ≠ 0 →
      bernoulliKL ((mv base).μ j) ((mv (alt j)).μ j) ≤ C) :
    ∃ (F : Finset (Site → State)),
      F.card = Fintype.card State ^ P.card ∧
      ∀ c ∈ F, (↑(k - 1) : ℝ) * (bernoulliKL (1/3) (2/3) / C) ≤
        expectedTotal A (mv c) := by
  obtain ⟨F, hF_mem, hF_card⟩ := family_exponentially_many base P
  exact ⟨F, hF_card, fun c hc =>
    lower_bound_transfers mv A base c
      (peripheral_invariance mv support hds base P hP_disj c (hF_mem c hc)) _
      (composed_lower_bound mv support hds base alt halt_mod A hk
        hP0 hP1 C hC hkl_pos hkl_ub)⟩

end TemplateBridge
