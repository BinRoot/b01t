import Mathlib

/-!
# OracleCostProof

**Oracle calculation proof.**

This file does not formalize the rollout semantics. It formalizes the
resource-accounting algebra for one coherent fixed-horizon Sway rollout oracle,
separating semantic correctness of the oracle from arithmetic composition of
its cost.

The implementation is modeled by four nonnegative coefficients:
- `cSel`: cost per cell per counter bit in one selector pass,
- `cSway`: cost per cell in one synchronous Sway update round,
- `cCount`: cost per cell per counter bit for the black/white counting stage,
- `cCmp`: cost per majority-comparison pattern.

The selector/counter width is an external natural `w`. The paper instantiates
`w` as `ceil(log2 (N+1))`.

The main theorem is `oracleOpCost_formula`, which gives an exact closed form
for the operation count of one oracle call:

`H * (4 * cSel * N * w + cSway * N)
 + (2 * cCount * N * w + cCmp * (N + 1) * (N + 1) * (2 * w))`.

This is the formal arithmetic core behind the paper statement
`O(H N w + N^2 w)`.
-/

namespace SwayOracleCost

/-- Cost of one selector pass over all `N` cells with a `w`-bit counter. -/
def selectorPassCost (N w cSel : Nat) : Nat :=
  cSel * N * w

/-- Per-round selector cost: black compute/uncompute and white compute/uncompute. -/
def selectorRoundCost (N w cSel : Nat) : Nat :=
  4 * selectorPassCost N w cSel

/-- Cost of one synchronous Sway-update round. -/
def swayRoundCost (N cSway : Nat) : Nat :=
  cSway * N

/-- Cost of one counting pass into a `w`-bit sum register over all `N` cells. -/
def countPassCost (N w cCount : Nat) : Nat :=
  cCount * N * w

/--
Cost of the current majority-marking stage.

This models the naive implementation that iterates over all pairs
`(black, white) ∈ {0, ..., N}²` and applies a pattern-controlled operation on
`2*w` controls whenever `black > white`.
-/
def majorityCompareCost (N w cCmp : Nat) : Nat :=
  cCmp * (N + 1) * (N + 1) * (2 * w)

/-- Terminal payoff cost: count black/white, mark majority, then uncompute counts. -/
def payoffCost (N w cCount cCmp : Nat) : Nat :=
  2 * countPassCost N w cCount + majorityCompareCost N w cCmp

/-- Total operation count for one coherent fixed-horizon rollout oracle call. -/
def oracleOpCost (N H w cSel cSway cCount cCmp : Nat) : Nat :=
  H * (selectorRoundCost N w cSel + swayRoundCost N cSway) +
    payoffCost N w cCount cCmp

/-- Cost of one selector round in closed form. -/
theorem selectorRoundCost_formula (N w cSel : Nat) :
    selectorRoundCost N w cSel = 4 * cSel * N * w := by
  unfold selectorRoundCost selectorPassCost
  ring

/-- Payoff cost in closed form. -/
theorem payoffCost_formula (N w cCount cCmp : Nat) :
    payoffCost N w cCount cCmp =
      2 * cCount * N * w + cCmp * (N + 1) * (N + 1) * (2 * w) := by
  unfold payoffCost countPassCost majorityCompareCost
  ring

/-- Exact closed form for one oracle call. -/
theorem oracleOpCost_formula (N H w cSel cSway cCount cCmp : Nat) :
    oracleOpCost N H w cSel cSway cCount cCmp =
      H * (4 * cSel * N * w + cSway * N) +
        (2 * cCount * N * w + cCmp * (N + 1) * (N + 1) * (2 * w)) := by
  unfold oracleOpCost swayRoundCost
  rw [selectorRoundCost_formula, payoffCost_formula]

/--
Decomposition: separate bounds for per-round selector work, per-round Sway work,
and the terminal payoff work compose to a bound on the whole oracle cost.
-/
theorem oracleOpCost_le_of_component_bounds
    {N H w cSel cSway cCount cCmp selB swayB payB : Nat}
    (hSel : selectorRoundCost N w cSel ≤ selB)
    (hSway : swayRoundCost N cSway ≤ swayB)
    (hPay : payoffCost N w cCount cCmp ≤ payB) :
    oracleOpCost N H w cSel cSway cCount cCmp ≤ H * (selB + swayB) + payB := by
  unfold oracleOpCost
  gcongr

/--
Specialized bound using the closed forms above. This is the exact arithmetic
statement rendered in the paper as `T_oracle(N,H) = O(H*N*w + N^2*w)`.
-/
theorem oracleOpCost_le_shape (N H w cSel cSway cCount cCmp : Nat) :
    oracleOpCost N H w cSel cSway cCount cCmp ≤
      H * (4 * cSel * N * w + cSway * N) +
        (2 * cCount * N * w + cCmp * (N + 1) * (N + 1) * (2 * w)) := by
  rw [oracleOpCost_formula]

/-- Shared qubits outside the `H` rollout rounds. -/
def sharedQubitCost (qShared : Nat) : Nat := qShared

/-- Qubits contributed by one rollout round. -/
def roundQubitCost (qRound : Nat) : Nat := qRound

/-- Total qubit count for the coherent oracle. -/
def oracleQubitCost (H qShared qRound : Nat) : Nat :=
  sharedQubitCost qShared + H * roundQubitCost qRound

/-- Exact qubit-count formula. -/
theorem oracleQubitCost_formula (H qShared qRound : Nat) :
    oracleQubitCost H qShared qRound = qShared + H * qRound := by
  rfl

/-- Total quantum cost for `qCalls` coherent oracle invocations. -/
def quantumTotalCost
    (qCalls N H w cSel cSway cCount cCmp : Nat) : Nat :=
  qCalls * oracleOpCost N H w cSel cSway cCount cCmp

/-- Exact formula for the total quantum cost. -/
theorem quantumTotalCost_formula
    (qCalls N H w cSel cSway cCount cCmp : Nat) :
    quantumTotalCost qCalls N H w cSel cSway cCount cCmp =
      qCalls *
        (H * (4 * cSel * N * w + cSway * N) +
          (2 * cCount * N * w + cCmp * (N + 1) * (N + 1) * (2 * w))) := by
  unfold quantumTotalCost
  rw [oracleOpCost_formula]

/-- Total classical cost for `rCalls` classical sampled rollouts with per-rollout cost `cRoll`. -/
def classicalTotalCost (rCalls cRoll : Nat) : Nat :=
  rCalls * cRoll

end SwayOracleCost
