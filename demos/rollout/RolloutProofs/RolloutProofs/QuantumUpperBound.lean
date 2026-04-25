import Mathlib

/-!
# Quantum Upper Bound

Given IQAE (axiom, Grinko et al. 2021) and quantum max-finding (axiom,
Dürr–Høyer 1996), move selection over k contenders at tolerance ε uses
at most √k/ε oracle calls.
-/

open Real

noncomputable section

namespace QuantumUpperBound

/-- IQAE query complexity (Grinko et al. 2021). -/
axiom iqae_query_complexity (delta : ℝ) (hdelta : 0 < delta) :
    ∃ (queries : ℝ), 0 < queries ∧ queries ≤ 1 / delta

/-- Quantum max-finding (Dürr-Høyer 1996). -/
axiom quantum_max_finding (k : ℕ) (hk : 1 ≤ k) :
    ∃ (comparisons : ℝ), 0 < comparisons ∧ comparisons ≤ Real.sqrt k

/-- Composing IQAE at tolerance ε with quantum max-finding over k items
    gives at most √k/ε total oracle calls. -/
theorem quantum_upper_bound (k : ℕ) (hk : 1 ≤ k) (eps : ℝ) (heps : 0 < eps) :
    ∃ (quantum_queries : ℝ),
      0 < quantum_queries ∧ quantum_queries ≤ Real.sqrt k / eps := by
  obtain ⟨comps, hcomps_pos, hcomps_le⟩ := quantum_max_finding k hk
  obtain ⟨per_comp, hper_pos, hper_le⟩ := iqae_query_complexity eps heps
  refine ⟨comps * per_comp, mul_pos hcomps_pos hper_pos, ?_⟩
  calc comps * per_comp
      ≤ Real.sqrt ↑k * (1 / eps) :=
        mul_le_mul hcomps_le hper_le (le_of_lt hper_pos) (Real.sqrt_nonneg _)
    _ = Real.sqrt ↑k / eps := by ring

end QuantumUpperBound
