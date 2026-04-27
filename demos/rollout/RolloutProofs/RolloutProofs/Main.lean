import RolloutProofs.RankSelectUniversality
import RolloutProofs.RankSelectUpperBound
import RolloutProofs.RankSelectCommunication
import RolloutProofs.RolloutLowerBound
import RolloutProofs.SwayDynamics
import RolloutProofs.QuantumUpperBound
import RolloutProofs.ManyHardBoards
import RolloutProofs.GeneralizedLifting
import RolloutProofs.AverageCaseHardness
import RolloutProofs.MoveValues
import RolloutProofs.OracleCostProof
import RolloutProofs.SpatialDecay
import RolloutProofs.TemplateBridge
import RolloutProofs.ApproximateBridge
import RolloutProofs.RankSelectCircuit
import RolloutProofs.RankSelectGateLowerBound
import RolloutProofs.RankSelectBlocked

/-!
# Summary

## File map

- `BanditCore`: shared definitions - `BanditInstance`, `IsEpsOptimal`,
  `bernoulliKL`, information-theoretic axioms.
- `RolloutLowerBound`: hard family, unique eps-optimality, Omega(k/eps^2) lower bound.
- `SwayDynamics`: board model, one-step locality, transmission bounds.
- `QuantumUpperBound`: IQAE plus Durr-Hoyer composition giving sqrt(k)/eps oracle calls.
- `MoveValues`: concrete `moveValues`, local score, invariance bridge.
- `OracleCostProof`: oracle resource accounting (op-count, qubit-count).
- `ManyHardBoards`: value-invariance lifting - shared move values imply shared hardness.
- `GeneralizedLifting`: approximate-invariance lifting - bounded influence implies hardness (non-local).
- `SpatialDecay`: geometric influence decay; lifting is non-trivial even when H exceeds grid diameter.
- `TemplateBridge`: composition - disjoint support gives agreement, hence Omega(k/eps^2) on exponentially many configs.
- `ApproximateBridge`: approximate version - correctness plus lifting gives a bound on the perturbed family.
- `RankSelectGateLowerBound`: summed-cut Omega(Nw/kappa^2) gate lower bound via cuts.

## Headline results

- **Classical lower bound** (`SwayRollout.main_lower_bound`):
  E₀[τ] ≥ (k−1) · ln 2 / (288 ε²) for any (ε, 2/3)-correct algorithm.

- **Quantum upper bound** (`QuantumUpperBound.quantum_upper_bound`):
  ≤ √k/ε oracle calls via IQAE + quantum max-finding.

- **Move-value invariance** (`SwayMoveValues.moveValues_invariance`):
  Boards agreeing on N_H(G) with shared exterior occupancy have
  identical rollout-value vectors. Proved via the H-step induction
  `rollout_terminal_agree_on_G`, which applies `prop2_locality`
  inductively with occupancy preservation.

- **Many hard boards** (`SwayManyHardBoards.value_invariance_implies_hardness`):
  Value invariance + hard witness ⟹ hardness on the entire family.

- **Generalized lifting** (`GeneralizedLifting.hardness_from_bounded_influence`):
  Bounded per-site influence + gap on witness + peripheral inertness
  ⟹ ε-optimality on an exponential family. Extends the lifting to
  non-local dynamics without requiring exact invariance.

- **Template bridge** (`TemplateBridge.lower_bound_on_exponential_family`):
  Composes the lower bound with the lifting via arm-disjoint locality:
  disjoint support regions → inter-instance agreement (for B–H) →
  Ω(k/ε²) on the base → transferred to |State|^|P| configurations.

- **Rank-select gate lower bound** (`CircuitWithCuts.gate_lower_bound`):
  For a bit-level bounded-fan-in circuit (fan-in κ) on N ≥ 4 mask
  positions with a per-cut `RankSelectCircuit` extracted at every
  cut t ∈ [1, N), the gate count satisfies
  (N/4)·(⌊log₂ N⌋ − 2) ≤ 2κ·(κ − 1)·nGates. Closes the Ω(Nw/κ²) gap
  by summing `rankSelectCircuit_bits_lower_bound` over the window
  t ∈ [N/4, N/2) and chaining the gate-span inequality.

- **Approximate bridge** (`ApproximateBridge.lower_bound_perturbed_family`):
  Extends the composition to perturbed configurations (β < ε regime).
  Composes: bounded perturbation → gap preservation → unique ε-optimality
  → correctness gives output bounds → per-config lower bound →
  Ω(k/ε²) on |State|^|P| configurations.
  Includes `average_case_lower_bound` for the ε < β < 2ε regime.

## External axioms

The following are axiomatized external results (not project-specific):

- `bretagnolle_huber_chain_rule` (Kaufmann et al. 2016, Lemma 1)
- `iqae_query_complexity` (Grinko et al. 2021)
- `quantum_max_finding` (Dürr-Høyer 1996)
- `BanditAlgorithm` interface (`expectedPulls`, `expectedTotal`, `outputProb`)
- `outputProb_nonneg`, `outputProb_sum_eq_one` (probability axioms)
-/
