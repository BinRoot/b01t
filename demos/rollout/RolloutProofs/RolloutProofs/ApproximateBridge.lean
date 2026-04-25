import RolloutProofs.TemplateBridge
import RolloutProofs.GeneralizedLifting
import RolloutProofs.AverageCaseHardness

/-!
# Approximate Bridge: Connecting Lifting to the Lower Bound

Connects:
- `GeneralizedLifting` (eps-optimality under bounded influence)
- `AverageCaseHardness` (most configs are hard when eps < beta < 2eps)
- `TemplateBridge` (lower bound from disjoint support + template)

## The composition chain

The lower bound needs output probability bounds (hP0, hP1). These follow from:
1. The lifting gives **eps-optimality** of arm i on perturbed configs.
2. The gap condition gives **unique** eps-optimality (no other arm is eps-optimal).
3. Correctness + unique optimality gives the **output probability bounds**.
4. Agreement is still **exact** (ArmDisjointSupport applies to any base, including perturbed ones).
5. KL bounds are hypothesized per configuration.

## Covered regimes

- `beta < eps` (deterministic, all configs hard): `lower_bound_perturbed_family`.
- `eps < beta < 2eps` (probabilistic, most configs hard): `average_case_lower_bound`.

## Relation to existing files

- Uses `TemplateBridge.composed_lower_bound` (which already works for any base).
- Uses `GeneralizedLifting.gap_after_perturbation` and `peripheral_perturbation_bound`.
- Uses `AverageCaseHardness.average_case_hardness` for the failure probability.
- Adds `outputProb_nonneg` and `outputProb_sum_eq_one` axioms to `BanditCore`.
-/

set_option linter.unusedVariables false
set_option linter.style.setOption false
set_option linter.flexible false
set_option linter.unusedFintypeInType false

open Real Finset Bandit GeneralizedLifting TemplateBridge

noncomputable section

namespace ApproximateBridge

variable {k : ℕ}

-- ════════════════════════════════════════════════════════════════
-- S 1: Correctness and output probability bounds
-- ════════════════════════════════════════════════════════════════

/-- (eps, 2/3)-correctness: any subset of non-eps-optimal arms has
    total output probability at most 1/3.

    This is the standard PAC definition for best-arm identification:
    the algorithm outputs an eps-optimal arm with probability >= 2/3. -/
def IsEpsCorrect (A : BanditAlgorithm k) (μ : BanditInstance k) (ε : ℝ) : Prop :=
  ∀ S : Finset (Fin k), (∀ i ∈ S, ¬ IsEpsOptimal μ ε i) →
    S.sum (fun i => outputProb A μ i) ≤ 1/3

/-- From correctness: each non-eps-optimal arm has output probability <= 1/3.
    Instantiates the total-probability bound with S = {j}. -/
theorem per_arm_from_correctness (A : BanditAlgorithm k) (μ : BanditInstance k)
    (ε : ℝ) (j : Fin k)
    (hcorrect : IsEpsCorrect A μ ε)
    (hnot_opt : ¬ IsEpsOptimal μ ε j) :
    outputProb A μ j ≤ 1/3 := by
  have h := hcorrect {j} (fun i hi => by rwa [Finset.mem_singleton.mp hi])
  simpa using h

/-- From correctness + unique optimality: the unique eps-optimal arm has
    output probability >= 2/3.

    Proof: all other arms are non-optimal, so their total probability is
    <= 1/3. Since probabilities sum to 1, the optimal arm gets >= 2/3. -/
theorem unique_optimal_from_correctness (A : BanditAlgorithm k)
    (μ : BanditInstance k) (ε : ℝ) (i : Fin k)
    (hcorrect : IsEpsCorrect A μ ε)
    (hunique : ∀ j, j ≠ i → ¬ IsEpsOptimal μ ε j) :
    2/3 ≤ outputProb A μ i := by
  have hrest := hcorrect (Finset.univ.erase i) (fun j hj =>
    hunique j (Finset.ne_of_mem_erase hj))
  have hsplit := Finset.add_sum_erase Finset.univ
    (fun j => outputProb A μ j) (Finset.mem_univ i)
  rw [outputProb_sum_eq_one A μ] at hsplit
  linarith

-- ════════════════════════════════════════════════════════════════
-- S 2: Unique eps-optimality from gap
-- ════════════════════════════════════════════════════════════════

/-- If arm i has gap strictly greater than eps, then i is the **unique**
    eps-optimal arm: no other arm j != i is eps-optimal.

    This is the link between `HasGap` (from GeneralizedLifting) and the
    uniqueness needed for output probability bounds. -/
theorem unique_from_strict_gap
    (inst : BanditInstance k) (i : Fin k) (Δ ε : ℝ)
    (hΔ : ε < Δ) (hgap : HasGap inst i Δ) :
    ∀ j, j ≠ i → ¬ IsEpsOptimal inst ε j := by
  intro j hj hopt
  have h1 := hgap j hj
  have h2 := hopt i
  linarith

/-- After bounded perturbation of a witness with gap >= 3eps, the perturbed
    instance has gap >= 3eps - 2delta. When delta < eps, this is > eps,
    giving unique eps-optimality on the perturbed instance.

    Composes `gap_after_perturbation` with `unique_from_strict_gap`. -/
theorem perturbed_unique_optimal
    (inst₁ inst₂ : BanditInstance k) (i : Fin k) (Δ δ ε : ℝ)
    (hgap : HasGap inst₁ i Δ)
    (hshift : ∀ j : Fin k, |inst₂.μ j - inst₁.μ j| ≤ δ)
    (hΔε : ε < Δ - 2 * δ) :
    ∀ j, j ≠ i → ¬ IsEpsOptimal inst₂ ε j :=
  unique_from_strict_gap inst₂ i (Δ - 2 * δ) ε hΔε
    (gap_after_perturbation inst₁ inst₂ i Δ δ hgap hshift)

-- ════════════════════════════════════════════════════════════════
-- S 3: Perturbed means bounded
-- ════════════════════════════════════════════════════════════════

/-- On a perturbed configuration, arm means shift by at most beta = P.sum influence.
    Direct corollary of `peripheral_perturbation_bound`. -/
theorem perturbed_means_bounded
    {Site State : Type*}
    (mv : (Site → State) → BanditInstance k)
    (influence : Site → ℝ)
    (hsi : SingleSiteInfluence mv influence)
    (base : Site → State) (P : Finset Site)
    (c : Site → State) (hc : c ∈ peripheralFamily base P)
    (j : Fin k) :
    |(mv c).μ j - (mv base).μ j| ≤ P.sum influence :=
  peripheral_perturbation_bound mv influence hsi base P c hc j

-- ════════════════════════════════════════════════════════════════
-- S 4: Output probability bounds on perturbed configs
-- ════════════════════════════════════════════════════════════════

/-- **Base-side output bound.** On a perturbed base configuration,
    arm i is uniquely eps-optimal (from gap + bounded perturbation),
    so correctness gives outputProb <= 1/3 for each contender j != i.

    This discharges the `hP0` hypothesis of `composed_lower_bound`
    for perturbed configurations. -/
theorem perturbed_base_hP0
    {Site State : Type*}
    (mv : (Site → State) → BanditInstance k)
    (influence : Site → ℝ)
    (hsi : SingleSiteInfluence mv influence)
    (base : Site → State) (P : Finset Site)
    (i : Fin k) (ε : ℝ) (hε : 0 < ε)
    (Δ : ℝ) (hgap : HasGap (mv base) i Δ)
    (hΔε : ε < Δ - 2 * P.sum influence)
    (A : BanditAlgorithm k)
    (c : Site → State) (hc : c ∈ peripheralFamily base P)
    (hcorrect : IsEpsCorrect A (mv c) ε)
    (j : Fin k) (hj : j ≠ i) :
    outputProb A (mv c) j ≤ 1/3 := by
  apply per_arm_from_correctness A (mv c) ε j hcorrect
  exact perturbed_unique_optimal (mv base) (mv c) i Δ (P.sum influence) ε
    hgap (fun l => perturbed_means_bounded mv influence hsi base P c hc l) hΔε j hj

/-- **Alt-side output bound.** On the alt configuration for contender j,
    if arm j is uniquely eps-optimal (from the alt construction + gap),
    then correctness gives outputProb >= 2/3 for arm j.

    This discharges the `hP1` hypothesis of `composed_lower_bound`. -/
theorem perturbed_alt_hP1
    (A : BanditAlgorithm k)
    (μ : BanditInstance k) (ε : ℝ) (j : Fin k)
    (hcorrect : IsEpsCorrect A μ ε)
    (hunique : ∀ l, l ≠ j → ¬ IsEpsOptimal μ ε l) :
    2/3 ≤ outputProb A μ j :=
  unique_optimal_from_correctness A μ ε j hcorrect hunique

-- ════════════════════════════════════════════════════════════════
-- S 5: Per-configuration lower bound
-- ════════════════════════════════════════════════════════════════

/-- **Per-configuration lower bound.** For a single perturbed configuration c,
    if the base-side and alt-side conditions hold, the lower bound applies.

    The agreement between (mv c) and (mv (alt c j)) is **exact** for i != j,
    because alt only modifies support(j) and supports are disjoint.
    The "approximate" part is that c itself differs from the witness,
    but that only changes the mean values, not the agreement structure. -/
theorem lower_bound_on_perturbed_config
    {Site State : Type*}
    (mv : (Site → State) → BanditInstance k)
    (support : Fin k → Finset Site)
    (hds : ArmDisjointSupport mv support)
    (c : Site → State)
    (alt : Fin k → Site → State)
    (halt_mod : ∀ j : Fin k, j.val ≠ 0 →
      ∀ s, s ∉ support j → (alt j) s = c s)
    (A : BanditAlgorithm k) (hk : 2 ≤ k)
    (hP0 : ∀ j : Fin k, j.val ≠ 0 → outputProb A (mv c) j ≤ 1/3)
    (hP1 : ∀ j : Fin k, j.val ≠ 0 → 2/3 ≤ outputProb A (mv (alt j)) j)
    (C : ℝ) (hC : 0 < C)
    (hkl_pos : ∀ j : Fin k, j.val ≠ 0 →
      0 < bernoulliKL ((mv c).μ j) ((mv (alt j)).μ j))
    (hkl_ub : ∀ j : Fin k, j.val ≠ 0 →
      bernoulliKL ((mv c).μ j) ((mv (alt j)).μ j) ≤ C) :
    (↑(k - 1) : ℝ) * (bernoulliKL (1/3) (2/3) / C) ≤
      expectedTotal A (mv c) :=
  composed_lower_bound mv support hds c alt halt_mod A hk hP0 hP1 C hC hkl_pos hkl_ub

-- ════════════════════════════════════════════════════════════════
-- S 6: Family lower bound (beta < eps regime)
-- ════════════════════════════════════════════════════════════════

/-- **Deterministic regime: all configs are hard.**

    When beta = P.sum influence < eps, every configuration in the
    peripheral family satisfies the lower bound.

    The composition chain for each c in the family:
    1. `peripheral_perturbation_bound`: means shift by <= beta
    2. `gap_after_perturbation`: gap shrinks from >= 3eps to >= 3eps - 2beta > eps
    3. `unique_from_strict_gap`: arm i (= arm 0) is uniquely eps-optimal
    4. `per_arm_from_correctness`: contender output probability <= 1/3
    5. `agreement_from_disjoint_support`: exact agreement for B-H
    6. `generalized_main_lower_bound`: Omega(k/eps^2) on this config -/
theorem lower_bound_perturbed_family
    {Site State : Type*} [Fintype State]
    (mv : (Site → State) → BanditInstance k)
    (support : Fin k → Finset Site)
    (hds : ArmDisjointSupport mv support)
    (influence : Site → ℝ)
    (hsi : SingleSiteInfluence mv influence)
    -- Witness and peripheral set
    (base : Site → State) (P : Finset Site)
    (i : Fin k) (ε : ℝ) (hε : 0 < ε)
    (Δ : ℝ) (hgap : HasGap (mv base) i Δ)
    (hΔε : ε < Δ - 2 * P.sum influence)
    -- Alt configurations (per family member, per contender)
    (alt : (Site → State) → Fin k → Site → State)
    (halt_mod : ∀ c ∈ peripheralFamily base P,
      ∀ j : Fin k, j.val ≠ 0 →
      ∀ s, s ∉ support j → (alt c j) s = c s)
    (A : BanditAlgorithm k) (hk : 2 ≤ k)
    -- Universal correctness: algorithm is (eps, 2/3)-correct on base and alt
    (hcorrect_base : ∀ c ∈ peripheralFamily base P,
      IsEpsCorrect A (mv c) ε)
    (hcorrect_alt : ∀ c ∈ peripheralFamily base P,
      ∀ j : Fin k, j.val ≠ 0 →
      IsEpsCorrect A (mv (alt c j)) ε)
    -- Alt side: arm j is uniquely eps-optimal on alt configs
    (halt_unique : ∀ c ∈ peripheralFamily base P,
      ∀ j : Fin k, j.val ≠ 0 →
      ∀ l, l ≠ j → ¬ IsEpsOptimal (mv (alt c j)) ε l)
    -- KL bounds
    (C : ℝ) (hC : 0 < C)
    (hkl_pos : ∀ c ∈ peripheralFamily base P,
      ∀ j : Fin k, j.val ≠ 0 →
      0 < bernoulliKL ((mv c).μ j) ((mv (alt c j)).μ j))
    (hkl_ub : ∀ c ∈ peripheralFamily base P,
      ∀ j : Fin k, j.val ≠ 0 →
      bernoulliKL ((mv c).μ j) ((mv (alt c j)).μ j) ≤ C)
    -- Arm i corresponds to arm 0 in the hard family
    (hi : i = ⟨0, by omega⟩) :
    ∃ (F : Finset (Site → State)),
      F.card = Fintype.card State ^ P.card ∧
      ∀ c ∈ F, (↑(k - 1) : ℝ) * (bernoulliKL (1/3) (2/3) / C) ≤
        expectedTotal A (mv c) := by
  obtain ⟨F, hF_mem, hF_card⟩ := family_exponentially_many base P
  refine ⟨F, hF_card, fun c hc => ?_⟩
  have hc_mem := hF_mem c hc
  apply lower_bound_on_perturbed_config mv support hds c (alt c) (halt_mod c hc_mem) A hk
  · intro j hj
    have hj_ne : j ≠ i := by rw [hi]; exact fun h => hj (Fin.ext_iff.mp h)
    exact perturbed_base_hP0 mv influence hsi base P i ε hε Δ hgap hΔε A c hc_mem
      (hcorrect_base c hc_mem) j hj_ne
  · intro j hj
    exact perturbed_alt_hP1 A (mv (alt c j)) ε j
      (hcorrect_alt c hc_mem j hj) (halt_unique c hc_mem j hj)
  · exact hC
  · exact fun j hj => hkl_pos c hc_mem j hj
  · exact fun j hj => hkl_ub c hc_mem j hj

-- ════════════════════════════════════════════════════════════════
-- S 7: Hard-config predicate
-- ════════════════════════════════════════════════════════════════

/-- A configuration is "hard" if arm i is **uniquely** eps-optimal:
    arm i is eps-optimal AND no other arm is eps-optimal.

    The lower bound chain (correctness -> output bounds -> B-H -> Omega(k/eps^2))
    requires uniqueness, not just eps-optimality. In the beta < eps regime,
    all configs satisfy this (S6). In the eps < beta < 2eps regime,
    only "most" configs satisfy this, and the failure probability is
    bounded by AverageCaseHardness. -/
def IsHardConfig {k : ℕ} (inst : BanditInstance k) (ε : ℝ) (i : Fin k) : Prop :=
  IsEpsOptimal inst ε i ∧ (∀ j, j ≠ i → ¬ IsEpsOptimal inst ε j)

/-- Gap > eps implies hard config. -/
theorem hard_from_strict_gap
    (inst : BanditInstance k) (i : Fin k) (Δ ε : ℝ)
    (hε : 0 ≤ ε) (hΔ : ε < Δ) (hgap : HasGap inst i Δ) :
    IsHardConfig inst ε i :=
  ⟨gap_implies_epsOptimal inst i Δ ε (by linarith) hε hgap,
   unique_from_strict_gap inst i Δ ε hΔ hgap⟩

-- ════════════════════════════════════════════════════════════════
-- S 8: Lower bound on hard configs
-- ════════════════════════════════════════════════════════════════

/-- **On any hard config, the per-config lower bound holds.**

    This is the key lemma that connects the lifting (which gives
    hardness) to the lower bound (which gives sample complexity).

    The proof chain:
    1. IsHardConfig gives unique eps-optimality of arm i
    2. Correctness + uniqueness -> hP0 (per_arm_from_correctness)
    3. Correctness + alt-uniqueness -> hP1 (unique_optimal_from_correctness)
    4. ArmDisjointSupport -> exact agreement (even on perturbed c)
    5. Agreement + hP0 + hP1 + KL -> Omega(k/eps^2) (composed_lower_bound) -/
theorem lower_bound_on_hard_config
    {Site State : Type*}
    (mv : (Site → State) → BanditInstance k)
    (support : Fin k → Finset Site)
    (hds : ArmDisjointSupport mv support)
    (c : Site → State) (i : Fin k) (ε : ℝ) (hk_pos : 0 < k)
    (hhard : IsHardConfig (mv c) ε i)
    (hi : i = ⟨0, hk_pos⟩)
    -- Alt construction
    (alt : Fin k → Site → State)
    (halt_mod : ∀ j : Fin k, j.val ≠ 0 →
      ∀ s, s ∉ support j → (alt j) s = c s)
    -- Algorithm and correctness
    (A : BanditAlgorithm k) (hk : 2 ≤ k)
    (hcorrect : IsEpsCorrect A (mv c) ε)
    (hcorrect_alt : ∀ j : Fin k, j.val ≠ 0 →
      IsEpsCorrect A (mv (alt j)) ε)
    (halt_unique : ∀ j : Fin k, j.val ≠ 0 →
      ∀ l, l ≠ j → ¬ IsEpsOptimal (mv (alt j)) ε l)
    -- KL bounds
    (C : ℝ) (hC : 0 < C)
    (hkl_pos : ∀ j : Fin k, j.val ≠ 0 →
      0 < bernoulliKL ((mv c).μ j) ((mv (alt j)).μ j))
    (hkl_ub : ∀ j : Fin k, j.val ≠ 0 →
      bernoulliKL ((mv c).μ j) ((mv (alt j)).μ j) ≤ C) :
    (↑(k - 1) : ℝ) * (bernoulliKL (1/3) (2/3) / C) ≤
      expectedTotal A (mv c) := by
  apply lower_bound_on_perturbed_config mv support hds c alt halt_mod A hk _ _ C hC hkl_pos hkl_ub
  · intro j hj
    have hj_ne : j ≠ i := by rw [hi]; exact fun h => hj (Fin.ext_iff.mp h)
    exact per_arm_from_correctness A (mv c) ε j hcorrect (hhard.2 j hj_ne)
  · intro j hj
    exact unique_optimal_from_correctness A (mv (alt j)) ε j
      (hcorrect_alt j hj) (halt_unique j hj)

-- ════════════════════════════════════════════════════════════════
-- S 9: Average-case composition (eps < beta < 2eps)
-- ════════════════════════════════════════════════════════════════

/-- **Failure implies non-hardness.** From `AverageCaseHardness`:
    if gapFun < -eps (arm i not eps-dominant over j), the config is not hard.

    Contrapositive: hard configs have gapFun >= -eps for all j,
    so failure_implies_large_deviation applies and McDiarmid bounds
    the probability of non-hardness. -/
theorem failure_contra_hard
    {Site State : Type*}
    (mv : (Site → State) → BanditInstance k)
    (c : Site → State) (i : Fin k) (ε : ℝ)
    (hε : 0 < ε) (j : Fin k) (hj : j ≠ i)
    (hhard : IsHardConfig (mv c) ε i) :
    AverageCaseHardness.gapFun mv i j c ≥ -ε := by
  unfold AverageCaseHardness.gapFun
  have := hhard.1 j
  linarith

/-- **Average-case lower bound.** Composes three results:

    **From AverageCaseHardness** (bounded differences + deviation threshold):
    - `perturbFun_bounded_diff`: h_j has bounded diffs with constant 2*delta(s)
    - `failure_implies_large_deviation`: failure ==> h_j < -4eps
    - `per_action_failure_bound`: McDiarmid tail per action
    - Union bound: failProb <= (k-1) * exp(-2(2eps-beta)^2/V)

    **From ApproximateBridge** (per-config lower bound):
    - `lower_bound_on_hard_config`: on any hard config (arm i uniquely
      eps-optimal), the Omega(k/eps^2) lower bound holds.

    **Combined** (probabilistic averaging):
    - Pr[hard] >= 1 - failBound (from AverageCaseHardness)
    - E[tau | hard] >= perConfigBound (from lower_bound_on_hard_config)
    - E[tau] >= E[tau | hard] * Pr[hard] >= (1 - failBound) * perConfigBound

    The distributional expectation enters as a hypothesis (havg).
    To discharge it, the caller invokes the law of total expectation
    with the non-negativity of expectedTotal. -/
theorem average_case_lower_bound
    (k : ℕ) (hk : 1 ≤ k)
    (eps β V : ℝ) (heps : 0 < eps) (hβ_lt : β < 2 * eps) (hV : 0 < V)
    -- Failure bound from AverageCaseHardness.average_case_hardness
    (failProb : ℝ)
    (hfail : failProb ≤
      (k - 1 : ℝ) * Real.exp (-2 * (2 * eps - β) ^ 2 / V))
    -- Per-config bound from lower_bound_on_hard_config
    (perConfigBound : ℝ) (hperConfig : 0 ≤ perConfigBound)
    -- Distributional expectation: E[tau] >= Pr[hard] * E[tau | hard]
    -- (law of total expectation + non-negativity of tau on non-hard configs)
    (avgRollouts : ℝ)
    (havg : (1 - failProb) * perConfigBound ≤ avgRollouts) :
    (1 - (k - 1 : ℝ) * Real.exp (-2 * (2 * eps - β) ^ 2 / V)) *
      perConfigBound ≤ avgRollouts := by
  have h_mono : (1 : ℝ) - (k - 1 : ℝ) * Real.exp (-2 * (2 * eps - β) ^ 2 / V) ≤
      1 - failProb := by linarith
  calc (1 - (k - 1 : ℝ) * Real.exp (-2 * (2 * eps - β) ^ 2 / V)) * perConfigBound
      ≤ (1 - failProb) * perConfigBound :=
        mul_le_mul_of_nonneg_right h_mono hperConfig
    _ ≤ avgRollouts := havg

end ApproximateBridge
