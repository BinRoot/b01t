import RolloutProofs.BanditCore

/-!
# Sway Rollout Lower Bound

Formalizes the Ω(k/ε²) lower bound on rollouts for ε-optimal move selection
in the Sway hard family.

## Contents
- Hard family construction and unique ε-optimality (§ 1–3)
- Bernoulli KL identity kl(1/3, 2/3) = ln 2 / 3 and bound kl(1/2, 1/2+6ε) ≤ 96ε² (§ 4–5)
- Main theorem: E₀[τ] ≥ (k−1) · ln 2 / (288 ε²) (§ 8)
-/

set_option linter.unusedVariables false
set_option linter.style.whitespace false
set_option linter.style.setOption false
set_option linter.flexible false

open Real Finset Bandit

noncomputable section

namespace SwayRollout

-- ════════════════════════════════════════════════════════════════
-- § 1: Hard family
-- ════════════════════════════════════════════════════════════════

def baseμ (ε : ℝ) {k : ℕ} (i : Fin k) : ℝ :=
  if i.val = 0 then 1/2 + 4 * ε else 1/2

def baseInstance (ε : ℝ) (k : ℕ) : BanditInstance k := ⟨baseμ ε⟩

def altμ (ε : ℝ) {k : ℕ} (j i : Fin k) : ℝ :=
  if i = j then 1/2 + 6 * ε
  else if i.val = 0 then 1/2 + 4 * ε
  else 1/2

def altInstance (ε : ℝ) (k : ℕ) (j : Fin k) : BanditInstance k := ⟨altμ ε j⟩

-- ════════════════════════════════════════════════════════════════
-- § 2: Unique ε-optimality
-- ════════════════════════════════════════════════════════════════

theorem base_arm0_epsOptimal (ε : ℝ) (hε : 0 < ε) (k : ℕ) (hk : 2 ≤ k) :
    IsEpsOptimal (baseInstance ε k) ε ⟨0, by omega⟩ := by
  intro j; simp only [baseInstance, baseμ, ite_true]; split_ifs <;> linarith

theorem base_armJ_not_epsOptimal (ε : ℝ) (hε : 0 < ε) (k : ℕ) (hk : 2 ≤ k)
    (j : Fin k) (hj : j.val ≠ 0) :
    ¬ IsEpsOptimal (baseInstance ε k) ε j := by
  intro h; have := h ⟨0, by omega⟩
  simp only [baseInstance, baseμ, ite_true, if_neg hj] at this; linarith

theorem alt_armJ_epsOptimal (ε : ℝ) (hε : 0 < ε) (k : ℕ) (hk : 2 ≤ k)
    (j : Fin k) (hj : j.val ≠ 0) :
    IsEpsOptimal (altInstance ε k j) ε j := by
  intro i; simp [altInstance, altμ]; split_ifs <;> linarith

theorem alt_armI_not_epsOptimal (ε : ℝ) (hε : 0 < ε) (k : ℕ) (hk : 2 ≤ k)
    (j : Fin k) (hj : j.val ≠ 0) (i : Fin k) (hi : i ≠ j) :
    ¬ IsEpsOptimal (altInstance ε k j) ε i := by
  intro h; have := h j
  simp [altInstance, altμ, if_neg hi] at this; split_ifs at this <;> linarith

-- ════════════════════════════════════════════════════════════════
-- § 3: ε-correctness ⟹ best-arm identification
-- ════════════════════════════════════════════════════════════════

theorem epsCorrect_implies_bestArm_base (ε : ℝ) (hε : 0 < ε)
    (k : ℕ) (hk : 2 ≤ k) (output : Fin k)
    (hopt : IsEpsOptimal (baseInstance ε k) ε output) :
    output = ⟨0, by omega⟩ := by
  by_contra h
  exact base_armJ_not_epsOptimal ε hε k hk output (fun heq => h (Fin.ext heq)) hopt

theorem epsCorrect_implies_bestArm_alt (ε : ℝ) (hε : 0 < ε)
    (k : ℕ) (hk : 2 ≤ k) (j : Fin k) (hj : j.val ≠ 0)
    (output : Fin k) (hopt : IsEpsOptimal (altInstance ε k j) ε output) :
    output = j := by
  by_contra h; exact alt_armI_not_epsOptimal ε hε k hk j hj output h hopt

-- ════════════════════════════════════════════════════════════════
-- § 4: KL identity
-- ════════════════════════════════════════════════════════════════

theorem kl_one_third_two_thirds :
    bernoulliKL (1/3) (2/3) = Real.log 2 / 3 := by
  unfold bernoulliKL
  rw [show (1:ℝ)/3 / (2/3) = 1/2 from by ring,
      show 1 - (1:ℝ)/3 = 2/3 from by ring,
      show 1 - (2:ℝ)/3 = 1/3 from by ring,
      show (2:ℝ)/3 / (1/3) = 2 from by ring,
      show Real.log (1/2 : ℝ) = -Real.log 2 from by rw [one_div, Real.log_inv]]
  ring

-- ════════════════════════════════════════════════════════════════
-- § 5: KL bounds
-- ════════════════════════════════════════════════════════════════

private theorem kl_half_form (ε : ℝ) (hε : 0 < ε) (hε24 : ε ≤ 1/24) :
    bernoulliKL (1/2) (1/2 + 6*ε) = -(1/2 : ℝ) * Real.log (1 - 144*ε^2) := by
  unfold bernoulliKL
  have hq : (0:ℝ) < 1/2 + 6*ε := by linarith
  have h1q : (0:ℝ) < 1/2 - 6*ε := by nlinarith
  rw [show 1 - (1/2 + 6*ε) = 1/2 - 6*ε from by ring,
      show (1:ℝ) - 1/2 = 1/2 from by ring]
  have hA : (1/2:ℝ) / (1/2 + 6*ε) ≠ 0 := by positivity
  have hB : (1/2:ℝ) / (1/2 - 6*ε) ≠ 0 := by positivity
  have hprod : (1/2:ℝ) / (1/2 + 6*ε) * ((1/2) / (1/2 - 6*ε)) = 1/(1 - 144*ε^2) := by
    rw [div_mul_div_comm]
    exact div_eq_div_iff (mul_ne_zero (ne_of_gt hq) (ne_of_gt h1q))
      (by nlinarith : (1:ℝ) - 144*ε^2 ≠ 0) |>.mpr (by ring)
  linarith [show Real.log (1/2/(1/2+6*ε)) + Real.log (1/2/(1/2-6*ε)) =
      -Real.log (1 - 144*ε^2) from by
    rw [← Real.log_mul hA hB, hprod, one_div, Real.log_inv]]

theorem bernoulliKL_pos (ε : ℝ) (hε : 0 < ε) (hε24 : ε ≤ 1/24) :
    0 < bernoulliKL (1/2) (1/2 + 6*ε) := by
  rw [kl_half_form ε hε hε24]
  nlinarith [Real.log_neg (by nlinarith : (0:ℝ) < 1 - 144*ε^2)
                          (by nlinarith : 1 - 144*ε^2 < 1)]

theorem bernoulliKL_le_96sq (ε : ℝ) (hε : 0 < ε) (hε24 : ε ≤ 1/24) :
    bernoulliKL (1/2) (1/2 + 6*ε) ≤ 96 * ε^2 := by
  rw [kl_half_form ε hε hε24]
  have h1mx : (0:ℝ) < 1 - 144*ε^2 := by nlinarith
  have hlog_inv := (Real.log_inv (1 - 144*ε^2)).symm
  have hlog_le := Real.log_le_sub_one_of_pos (by positivity : (0:ℝ) < (1-144*ε^2)⁻¹)
  have hinv_bound : (1 - 144*ε^2)⁻¹ - 1 ≤ 192*ε^2 := by
    have : (1-144*ε^2)⁻¹ - 1 = 144*ε^2 / (1-144*ε^2) := by field_simp; ring
    rw [this, div_le_iff₀ h1mx]; nlinarith [sq_nonneg ε, mul_le_mul hε24 hε24 (le_of_lt hε)
      (show (0:ℝ) ≤ 1/24 by linarith)]
  nlinarith

-- ════════════════════════════════════════════════════════════════
-- § 6: Per-arm lower bound
-- ════════════════════════════════════════════════════════════════

private theorem base_alt_agree (ε : ℝ) (k : ℕ) (j : Fin k) (hj : j.val ≠ 0) :
    ∀ i : Fin k, i ≠ j → (baseInstance ε k).μ i = (altInstance ε k j).μ i := by
  intro i hi; simp only [baseInstance, altInstance, baseμ, altμ, if_neg hi]

private theorem base_armJ_val (ε : ℝ) {k : ℕ} (j : Fin k) (hj : j.val ≠ 0) :
    (baseInstance ε k).μ j = 1/2 := by simp [baseInstance, baseμ, if_neg hj]

private theorem alt_armJ_val (ε : ℝ) {k : ℕ} (j : Fin k) :
    (altInstance ε k j).μ j = 1/2 + 6*ε := by simp [altInstance, altμ]

/-- Each contender j ≠ 0 requires ≥ ln 2 / (288 ε²) pulls under the base instance. -/
theorem per_arm_bound (ε : ℝ) (hε : 0 < ε) (hε24 : ε ≤ 1/24)
    (k : ℕ) (hk : 2 ≤ k) (A : BanditAlgorithm k)
    (j : Fin k) (hj : j.val ≠ 0)
    (hP0 : outputProb A (baseInstance ε k) j ≤ 1/3)
    (hP1 : 2/3 ≤ outputProb A (altInstance ε k j) j) :
    Real.log 2 / (288 * ε^2) ≤ expectedPulls A (baseInstance ε k) j := by
  have hkl_pos := bernoulliKL_pos ε hε hε24
  have hBH := bretagnolle_huber_chain_rule A _ _ j (base_alt_agree ε k j hj) hP0 hP1
    (by rw [base_armJ_val ε j hj, alt_armJ_val]; exact hkl_pos)
  rw [base_armJ_val ε j hj, alt_armJ_val] at hBH
  calc Real.log 2 / (288 * ε^2)
      = bernoulliKL (1/3) (2/3) / (96 * ε^2) := by rw [kl_one_third_two_thirds]; ring
    _ ≤ bernoulliKL (1/3) (2/3) / bernoulliKL (1/2) (1/2 + 6*ε) := by
        apply div_le_div_of_nonneg_left (by rw [kl_one_third_two_thirds]; positivity)
          hkl_pos (bernoulliKL_le_96sq ε hε hε24)
    _ ≤ expectedPulls A (baseInstance ε k) j := by rwa [div_le_iff₀ hkl_pos]

-- ════════════════════════════════════════════════════════════════
-- § 7: Main theorem
-- ════════════════════════════════════════════════════════════════

/-- **Main Theorem.** Any (ε, 2/3)-correct algorithm on the Sway hard family
    requires E₀[τ] ≥ (k−1) · ln 2 / (288 ε²). -/
theorem main_lower_bound (ε : ℝ) (hε : 0 < ε) (hε24 : ε ≤ 1/24)
    (k : ℕ) (hk : 2 ≤ k) (A : BanditAlgorithm k)
    (hP0 : ∀ j : Fin k, j.val ≠ 0 → outputProb A (baseInstance ε k) j ≤ 1/3)
    (hP1 : ∀ j : Fin k, j.val ≠ 0 → 2/3 ≤ outputProb A (altInstance ε k j) j) :
    (↑(k - 1) : ℝ) * (Real.log 2 / (288 * ε^2)) ≤ expectedTotal A (baseInstance ε k) := by
  set S := Finset.univ.erase (⟨0, by omega⟩ : Fin k)
  have hcard : S.card = k - 1 := by simp [S, card_erase_of_mem (mem_univ _)]
  have hper : ∀ j ∈ S, Real.log 2 / (288*ε^2) ≤ expectedPulls A (baseInstance ε k) j := by
    intro j hj; simp [S, mem_erase, Fin.ext_iff] at hj
    exact per_arm_bound ε hε hε24 k hk A j hj (hP0 j hj) (hP1 j hj)
  calc (↑(k-1) : ℝ) * (Real.log 2 / (288*ε^2))
      = S.card • (Real.log 2 / (288*ε^2)) := by rw [hcard, nsmul_eq_mul]
    _ ≤ S.sum (fun j => expectedPulls A (baseInstance ε k) j) :=
        card_nsmul_le_sum _ _ _ hper
    _ ≤ univ.sum (fun j => expectedPulls A (baseInstance ε k) j) :=
        sum_le_sum_of_subset_of_nonneg (erase_subset _ _)
          (fun j _ _ => expectedPulls_nonneg A _ j)
    _ ≤ expectedTotal A (baseInstance ε k) := total_ge_sum_pulls A _

end SwayRollout
