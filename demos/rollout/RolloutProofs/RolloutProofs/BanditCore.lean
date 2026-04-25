import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

/-!
# Bandit Core Definitions

Shared definitions for the bandit lower-bound files:

- `BanditInstance`: a k-armed bandit with mean vector μ
- `IsEpsOptimal`: arm i is ε-optimal if no arm beats it by more than ε
- `bernoulliKL`: Bernoulli KL divergence
- Abstract algorithm interface and Bretagnolle–Huber axiom
-/

open Real Finset

noncomputable section

namespace Bandit

structure BanditInstance (k : ℕ) where
  μ : Fin k → ℝ

def IsEpsOptimal {k : ℕ} (inst : BanditInstance k) (ε : ℝ) (i : Fin k) : Prop :=
  ∀ j : Fin k, inst.μ j - inst.μ i ≤ ε

noncomputable def bernoulliKL (p q : ℝ) : ℝ :=
  p * Real.log (p / q) + (1 - p) * Real.log ((1 - p) / (1 - q))

-- ════════════════════════════════════════════════════════════════
-- Abstract algorithm interface
-- ════════════════════════════════════════════════════════════════

axiom BanditAlgorithm : ℕ → Type
axiom expectedPulls : {k : ℕ} → BanditAlgorithm k → BanditInstance k → Fin k → ℝ
axiom expectedTotal : {k : ℕ} → BanditAlgorithm k → BanditInstance k → ℝ
axiom outputProb : {k : ℕ} → BanditAlgorithm k → BanditInstance k → Fin k → ℝ

axiom expectedPulls_nonneg {k : ℕ} (A : BanditAlgorithm k) (μ : BanditInstance k)
    (j : Fin k) : 0 ≤ expectedPulls A μ j

axiom outputProb_nonneg {k : ℕ} (A : BanditAlgorithm k) (μ : BanditInstance k)
    (i : Fin k) : 0 ≤ outputProb A μ i

axiom outputProb_sum_eq_one {k : ℕ} (A : BanditAlgorithm k) (μ : BanditInstance k) :
    Finset.univ.sum (fun i => outputProb A μ i) = 1

axiom total_ge_sum_pulls {k : ℕ} (A : BanditAlgorithm k) (μ : BanditInstance k) :
    (Finset.univ.sum fun j => expectedPulls A μ j) ≤ expectedTotal A μ

/-- Transportation lemma (Kaufmann, Cappé & Garivier 2016, Lemma 1),
    derived from Bretagnolle–Huber (Lattimore & Szepesvári, Thm 14.2)
    and divergence decomposition (Lattimore & Szepesvári, Lem 15.1). -/
axiom bretagnolle_huber_chain_rule
    {k : ℕ} (A : BanditAlgorithm k) (μ₀ μ₁ : BanditInstance k) (j : Fin k)
    (hagree : ∀ i : Fin k, i ≠ j → μ₀.μ i = μ₁.μ i)
    (hP0 : outputProb A μ₀ j ≤ 1/3) (hP1 : 2/3 ≤ outputProb A μ₁ j)
    (hkl_pos : 0 < bernoulliKL (μ₀.μ j) (μ₁.μ j)) :
    bernoulliKL (1/3) (2/3) ≤ expectedPulls A μ₀ j * bernoulliKL (μ₀.μ j) (μ₁.μ j)

end Bandit
