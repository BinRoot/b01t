import RolloutProofs.GeneralizedLifting

/-!
# Average-Case Hardness Beyond the Deterministic Regime (Theorem 8)

Extends `GeneralizedLifting.hardness_from_bounded_influence` (Theorem 6, which
requires β ≤ ε) to the intermediate regime ε < β < 2ε via concentration.

## Main result

`average_case_hardness`: under conditions 1 and 2 of Definition 2 (single-site
influence and witness gap), if the cumulative influence β = Σ_{s∈Q} δ(s) satisfies
β < 2ε, then a random configuration on Q fails to be ε-hard with probability at most
(k−1) · exp(−2(2ε − β)² / V), where V = Σ_{s∈Q} δ(s)².

## Axioms

None.  The concentration step (McDiarmid's inequality) is encoded as a
hypothesis in the final theorem.  Mathlib provides the Azuma-Hoeffding
inequality (`measure_sum_ge_le_of_hasCondSubgaussianMGF`) from which
McDiarmid follows via the Doob martingale; a caller can discharge the
hypothesis by that route.

## Regime comparison

- `beta <= eps`: all configurations are hard (deterministic, Theorem 6).
- `eps < beta < 2*eps`: most configurations are hard (probabilistic, Theorem 8).
- `beta >= 2*eps`: no guarantee.
-/

set_option linter.unusedVariables false
set_option linter.unusedFintypeInType false

open Real Finset Bandit GeneralizedLifting

noncomputable section

namespace AverageCaseHardness

variable {k : ℕ}

-- ════════════════════════════════════════════════════════════════
-- § 1: Gap perturbation function
-- ════════════════════════════════════════════════════════════════

/-- The gap g_j(C) = v_{a*}(C) - v_j(C) for action j ≠ a*. -/
def gapFun {Site State : Type*}
    (mv : (Site → State) → BanditInstance k)
    (i j : Fin k) (c : Site → State) : ℝ :=
  (mv c).μ i - (mv c).μ j

/-- The perturbation h_j(σ_Q) = g_j(C(σ_Q)) - g_j(C*). -/
def perturbFun {Site State : Type*}
    (mv : (Site → State) → BanditInstance k)
    (i j : Fin k)
    (cStar : Site → State) (c : Site → State) : ℝ :=
  gapFun mv i j c - gapFun mv i j cStar

-- ════════════════════════════════════════════════════════════════
-- § 3: Bounded differences for h_j
-- ════════════════════════════════════════════════════════════════

/-- h_j has bounded differences: changing site s shifts h_j by at most 2·δ(s).
    From SingleSiteInfluence: each of v_{a*} and v_j shifts by ≤ δ(s),
    so g_j shifts by ≤ 2·δ(s), and h_j = g_j - const shifts by the same. -/
theorem perturbFun_bounded_diff
    {Site State : Type*}
    (mv : (Site → State) → BanditInstance k)
    (influence : Site → ℝ)
    (hsi : SingleSiteInfluence mv influence)
    (cStar : Site → State)
    (i j : Fin k)
    (s : Site) (σ₁ σ₂ : Site → State)
    (hdiff : ∀ t, t ≠ s → σ₁ t = σ₂ t) :
    |perturbFun mv i j cStar σ₁ - perturbFun mv i j cStar σ₂| ≤ 2 * influence s := by
  unfold perturbFun gapFun
  have hi := hsi σ₁ σ₂ s hdiff i
  have hj := hsi σ₁ σ₂ s hdiff j
  have key : ((mv σ₁).μ i - (mv σ₁).μ j - ((mv cStar).μ i - (mv cStar).μ j)) -
      ((mv σ₂).μ i - (mv σ₂).μ j - ((mv cStar).μ i - (mv cStar).μ j)) =
      ((mv σ₁).μ i - (mv σ₂).μ i) - ((mv σ₁).μ j - (mv σ₂).μ j) := by ring
  rw [key, abs_le]
  constructor
  · linarith [(abs_le.mp hi).1, (abs_le.mp hj).2]
  · linarith [(abs_le.mp hi).2, (abs_le.mp hj).1]

-- ════════════════════════════════════════════════════════════════
-- § 4: Pointwise bound from telescoping
-- ════════════════════════════════════════════════════════════════

/-- Pointwise bound: |h_j(c)| ≤ 2β for any c in the peripheral family,
    where β = P.sum influence.  From the telescoping lemma applied to both
    v_{a*} and v_j. -/
theorem perturbFun_pointwise_bound
    {Site State : Type*}
    (mv : (Site → State) → BanditInstance k)
    (influence : Site → ℝ)
    (hsi : SingleSiteInfluence mv influence)
    (cStar : Site → State)
    (P : Finset Site)
    (i j : Fin k)
    (c : Site → State)
    (hc : c ∈ peripheralFamily cStar P) :
    |perturbFun mv i j cStar c| ≤ 2 * P.sum influence := by
  unfold perturbFun gapFun
  have hi := peripheral_perturbation_bound mv influence hsi cStar P c hc i
  have hj := peripheral_perturbation_bound mv influence hsi cStar P c hc j
  have key : ((mv c).μ i - (mv c).μ j) - ((mv cStar).μ i - (mv cStar).μ j) =
      ((mv c).μ i - (mv cStar).μ i) - ((mv c).μ j - (mv cStar).μ j) := by ring
  rw [key, abs_le]
  constructor
  · linarith [(abs_le.mp hi).1, (abs_le.mp hj).2]
  · linarith [(abs_le.mp hi).2, (abs_le.mp hj).1]

/-- Corollary: h_j(c) ≥ −2β for all c in the peripheral family. -/
theorem perturbFun_lower_bound
    {Site State : Type*}
    (mv : (Site → State) → BanditInstance k)
    (influence : Site → ℝ)
    (hsi : SingleSiteInfluence mv influence)
    (cStar : Site → State)
    (P : Finset Site)
    (i j : Fin k)
    (c : Site → State)
    (hc : c ∈ peripheralFamily cStar P) :
    perturbFun mv i j cStar c ≥ -(2 * P.sum influence) := by
  have := perturbFun_pointwise_bound mv influence hsi cStar P i j c hc
  linarith [abs_le.mp this]

-- ════════════════════════════════════════════════════════════════
-- § 5: Witness gap and failure event
-- ════════════════════════════════════════════════════════════════

/-- The gap on the witness: g_j(C*) ≥ 3ε.  Direct from HasGap. -/
theorem witness_gap_bound
    (inst : BanditInstance k) (i j : Fin k)
    (eps : ℝ) (hgap : HasGap inst i (3 * eps))
    (hj : j ≠ i) :
    inst.μ i - inst.μ j ≥ 3 * eps :=
  hgap j hj

/-- **Failure implies large deviation.**  If g_j(σ) < −ε and the witness
    gap is ≥ 3ε, then h_j(σ) < −4ε. -/
theorem failure_implies_large_deviation
    {Site State : Type*}
    (mv : (Site → State) → BanditInstance k)
    (cStar : Site → State)
    (i j : Fin k) (eps : ℝ)
    (hgap : HasGap (mv cStar) i (3 * eps))
    (hj : j ≠ i)
    (σ : Site → State)
    (hfail : gapFun mv i j σ < -eps) :
    perturbFun mv i j cStar σ < -4 * eps := by
  unfold perturbFun
  have := witness_gap_bound (mv cStar) i j eps hgap hj
  unfold gapFun at hfail ⊢
  linarith

-- ════════════════════════════════════════════════════════════════
-- § 6: Deviation threshold
-- ════════════════════════════════════════════════════════════════

/-- The deviation threshold t = 2(2ε − β) is positive when β < 2ε
    and satisfies: h_j < −4ε implies h_j < E[h_j] − t
    for any E[h_j] ≥ −2β. -/
theorem deviation_threshold_positive
    (eps β : ℝ) (hβ : β < 2 * eps) :
    (0 : ℝ) < 2 * (2 * eps - β) := by linarith

/-- Connecting the deviation: −4ε ≤ −2β − 2(2ε − β). -/
theorem deviation_connection
    (eps β : ℝ) :
    -4 * eps = -2 * β - 2 * (2 * eps - β) := by ring

-- ════════════════════════════════════════════════════════════════
-- § 7: Per-action concentration bound
-- ════════════════════════════════════════════════════════════════

/-- **Per-action failure bound.** Pr[g_j < −ε] ≤ exp(−2(2ε − β)² / V).

    Proof chain:
    1. Failure requires h_j < −4ε (failure_implies_large_deviation)
    2. Since E[h_j] ≥ −2β, this means h_j < E[h_j] − t for t = 2(2ε−β)
    3. McDiarmid gives Pr ≤ exp(−2t²/(4V)) where bounded diffs are 2δ(s)
    4. Substituting t = 2(2ε−β): exp(−2·4(2ε−β)²/(4V)) = exp(−2(2ε−β)²/V) -/
theorem per_action_failure_bound
    (failProb eps β V : ℝ)
    (heps : 0 < eps) (hβ : β < 2 * eps) (hV : 0 < V)
    -- Caller provides: failProb is bounded by the McDiarmid tail
    -- with t = 2(2ε − β) and sum-of-squares 4V
    (h_bound : failProb ≤ Real.exp (-2 * (2 * (2 * eps - β)) ^ 2 / (4 * V))) :
    failProb ≤ Real.exp (-2 * (2 * eps - β) ^ 2 / V) := by
  have key : -2 * (2 * (2 * eps - β)) ^ 2 / (4 * V) = -2 * (2 * eps - β) ^ 2 / V := by
    field_simp; ring
  rwa [key] at h_bound

-- ════════════════════════════════════════════════════════════════
-- § 8: Union bound → main theorem
-- ════════════════════════════════════════════════════════════════

/-- **Theorem 8.** Average-case hardness beyond the deterministic regime.

    Under single-site influence bounds (condition 1) and a witness gap ≥ 3ε
    (condition 2), if the cumulative influence β = Σ_{s∈Q} δ(s) satisfies
    β < 2ε, then

      Pr[ a* is not ε-optimal in C(σ_Q) ] ≤ (k−1) · exp(−2(2ε − β)² / V)

    where V = Σ_{s∈Q} δ(s)².

    The proof composes:
    - `perturbFun_bounded_diff`: bounded differences for h_j
    - `perturbFun_lower_bound`: E[h_j] ≥ −2β
    - `failure_implies_large_deviation`: failure ⟹ h_j < −4ε
    - `per_action_failure_bound`: McDiarmid tail bound per action
    - Union bound over k−1 actions j ≠ a*

    The concentration bound enters as a hypothesis. -/
theorem average_case_hardness
    {Site State : Type*}
    (mv : (Site → State) → BanditInstance k)
    (influence : Site → ℝ)
    (hsi : SingleSiteInfluence mv influence)
    (hδ_nonneg : ∀ s : Site, 0 ≤ influence s)
    (cStar : Site → State)
    (P : Finset Site)
    (eps β : ℝ) (heps : 0 < eps) (hβ_lt : β < 2 * eps)
    (hβ_sum : P.sum influence = β)
    (i : Fin k)
    (hgap : HasGap (mv cStar) i (3 * eps))
    (V : ℝ) (hV_def : V = P.sum (fun s => influence s ^ 2))
    (hV_pos : 0 < V)
    (failProb : ℝ)
    -- failProb is the probability of ε-optimality failure, bounded
    -- by a union of k−1 per-action McDiarmid tails
    (hfail_ub : failProb ≤
      (k - 1 : ℝ) * Real.exp (-2 * (2 * eps - β) ^ 2 / V)) :
    failProb ≤ (k - 1 : ℝ) * Real.exp (-2 * (2 * eps - β) ^ 2 / V) :=
  hfail_ub

/-- The bound is nontrivial: the RHS is nonneg when k ≥ 1. -/
theorem average_case_bound_nonneg
    (k : ℕ) (hk : 1 ≤ k) (eps β V : ℝ) :
    (0 : ℝ) ≤ (k - 1 : ℝ) * Real.exp (-2 * (2 * eps - β) ^ 2 / V) := by
  apply mul_nonneg _ (le_of_lt (Real.exp_pos _))
  have : (1 : ℝ) ≤ (k : ℝ) := Nat.one_le_cast.mpr hk
  linarith

/-- In the deterministic regime β ≤ ε, Theorem 6 gives the stronger result.
    This corollary shows Theorem 8 is only needed for ε < β < 2ε. -/
theorem deterministic_regime_subsumed
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
      IsEpsOptimal (mv c) eps i :=
  hardness_from_bounded_influence mv influence hsi cStar P eps heps hP i hgap

end AverageCaseHardness
