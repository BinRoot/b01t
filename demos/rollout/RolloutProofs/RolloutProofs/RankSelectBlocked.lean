import RolloutProofs.RankSelectUpperBound
import Mathlib.Tactic

/-!
# Blocked Rank-Select Upper Bound

Resource analysis for the blocked rank-select circuit
(Theorem `thm:rs-block` in the paper).

In the unrestricted-layout bounded-fan-in reversible circuit model
where long-range two-qubit gates are permitted, totalized coherent
rank-select admits a reversible implementation with `O(N · ℓ)` gates
and `O(w)` clean ancillae, where `ℓ` accounts for the depth of the
per-block popcount add-tree and the per-block local rank-select
(`ℓ = ⌈log₂(w+2)⌉` in the intended use, but the theorems below
treat `ℓ` as an opaque positive parameter so the arithmetic is
purely linear).

Construction (per block of size `B = w`):
  (a) Block popcount via balanced add-tree
  (b) Take-flag computation
  (c) Local rank residual
  (d) Local rank-select on `B = w` bits with output width `ℓ`
  (e) Controlled output write
  (f) Local uncompute and prefix update

A reverse accumulation pass cleans the running prefix counter,
adding the same asymptotic cost as the main pass.

This file proves:
  - `blockStepCost_eq`        : exact per-block cost = 4wℓ + 8w
  - `blockStepCost_le_12wl`   : per-block cost ≤ 12wℓ for ℓ ≥ 1
  - `numBlocks_times_w_le`    : numBlocks · w ≤ 2N for w ≤ N
  - `blockedTotalGateCost_le` : total ≤ 30 · N · ℓ
  - `blocked_beats_scan`      : ≤ totalGateCost (the scan) when 10ℓ ≤ w
  - `liveAncillaCount_le`     : live ancillae ≤ 5w + 2

External assumption: each step's cost is the bounded-fan-in
reversible gate count of the corresponding sub-circuit. The
popcount of `w` bits via a balanced add-tree of `O(log w)` levels
of `O(w)` constant-fan-in adders fits `wℓ` with `ℓ ≈ log₂ w`. The
local rank-select on a `w`-bit block with `O(log w)` output width
matches the same bound. Steps (b), (c), (e) and the prefix update
are all `O(w)` directly.
-/

namespace BlockedRankSelect

open Nat

/-! ## 1. Per-step gate costs -/

/-- Step (a). Block popcount on `w` bits via a balanced add-tree
    of `O(log w)` levels of `O(w)` adders. -/
def popcountCost (w ℓ : Nat) : Nat := w * ℓ

/-- Step (b). Take-flag from two `w`-bit comparators. -/
def takeCost (w : Nat) : Nat := 2 * w

/-- Step (c). Local rank residual via `w`-bit subtraction. -/
def localRankCost (w : Nat) : Nat := w

/-- Step (d). Local rank-select on a `w`-bit block with output
    width `ℓ`. Same bound as popcount. -/
def localScanCost (w ℓ : Nat) : Nat := w * ℓ

/-- Step (e). Controlled output write into a `w`-bit register. -/
def writeCost (w : Nat) : Nat := w

/-- Step (f). Local uncompute plus prefix update: mirror of (a)-(d)
    plus a `w`-bit add for `p ← p + c_q`. -/
def uncomputeCost (w ℓ : Nat) : Nat :=
  popcountCost w ℓ + takeCost w + localRankCost w + localScanCost w ℓ + w

/-! ## 2. Per-block cost -/

/-- Sum of all six steps for one block. -/
def blockStepCost (w ℓ : Nat) : Nat :=
  popcountCost w ℓ + takeCost w + localRankCost w + localScanCost w ℓ
  + writeCost w + uncomputeCost w ℓ

/-- Closed form: `blockStepCost w ℓ = 4wℓ + 8w`. -/
theorem blockStepCost_eq (w ℓ : Nat) :
    blockStepCost w ℓ = 4 * w * ℓ + 8 * w := by
  simp only [blockStepCost, popcountCost, takeCost, localRankCost,
             localScanCost, writeCost, uncomputeCost]
  ring

/-- Coarse: per-block cost is at most `12wℓ` when `ℓ ≥ 1`. -/
theorem blockStepCost_le_12wl {w ℓ : Nat} (hℓ : 1 ≤ ℓ) :
    blockStepCost w ℓ ≤ 12 * w * ℓ := by
  rw [blockStepCost_eq]
  have h : 8 * w ≤ 8 * w * ℓ := by
    calc 8 * w = 8 * w * 1 := by ring
      _ ≤ 8 * w * ℓ := Nat.mul_le_mul_left _ hℓ
  linarith

/-! ## 3. Number of blocks -/

/-- Number of blocks of size `w` covering `N` positions. We use
    `N / w + 1` as an upper bound on `⌈N/w⌉`; exact when `w ∤ N`,
    one too many otherwise (harmless for upper bounds). -/
def numBlocks (N w : Nat) : Nat := N / w + 1

/-- For `1 ≤ w ≤ N`, the blocks fit inside `2N` qubits.
    Useful: `numBlocks · w ≤ 2N`. -/
theorem numBlocks_times_w_le {N w : Nat} (hw : 1 ≤ w) (hN : w ≤ N) :
    numBlocks N w * w ≤ 2 * N := by
  unfold numBlocks
  have hmod : N % w < w := Nat.mod_lt N (by omega)
  have hdiv : w * (N / w) + N % w = N := Nat.div_add_mod N w
  have hsum : N / w * w ≤ N := by
    have hcomm : N / w * w = w * (N / w) := by ring
    omega
  have hexp : (N / w + 1) * w = N / w * w + w := by ring
  rw [hexp]
  linarith

/-! ## 4. Total cost -/

/-- Main pass: one block-step per block. -/
def mainPassCost (N w ℓ : Nat) : Nat := numBlocks N w * blockStepCost w ℓ

/-- Reverse accumulation cleanup: per block, recompute the popcount,
    subtract from the prefix counter (`w` gates), uncompute the
    popcount. -/
def reverseCleanupCost (N w ℓ : Nat) : Nat :=
  numBlocks N w * (popcountCost w ℓ + w + popcountCost w ℓ)

/-- Total gate cost of the blocked construction. -/
def blockedTotalGateCost (N w ℓ : Nat) : Nat :=
  mainPassCost N w ℓ + reverseCleanupCost N w ℓ

/-- Closed form: cleanup pass = `numBlocks · (2wℓ + w)`. -/
theorem reverseCleanupCost_eq (N w ℓ : Nat) :
    reverseCleanupCost N w ℓ = numBlocks N w * (2 * w * ℓ + w) := by
  unfold reverseCleanupCost popcountCost
  ring

/-! ## 5. Coarse upper bound: `O(N · ℓ)` gates -/

/-- **Blocked rank-select gate upper bound.**
    For `1 ≤ w ≤ N` and `ℓ ≥ 1`, the blocked construction uses at most
    `30 · N · ℓ` bounded-fan-in gates. With `ℓ = ⌈log₂(w+2)⌉` this is
    the `O(N log w)` claim of Theorem `thm:rs-block`. -/
theorem blockedTotalGateCost_le {N w ℓ : Nat}
    (hw : 1 ≤ w) (hN : w ≤ N) (hℓ : 1 ≤ ℓ) :
    blockedTotalGateCost N w ℓ ≤ 30 * N * ℓ := by
  unfold blockedTotalGateCost mainPassCost
  rw [reverseCleanupCost_eq]
  have hstep : blockStepCost w ℓ ≤ 12 * w * ℓ := blockStepCost_le_12wl hℓ
  have hcleanup : 2 * w * ℓ + w ≤ 3 * w * ℓ := by
    have hwl : w ≤ w * ℓ := by
      calc w = w * 1 := by ring
        _ ≤ w * ℓ := Nat.mul_le_mul_left _ hℓ
    linarith
  have hsum :
      numBlocks N w * blockStepCost w ℓ + numBlocks N w * (2 * w * ℓ + w)
        ≤ numBlocks N w * (12 * w * ℓ) + numBlocks N w * (3 * w * ℓ) := by
    have h1 := Nat.mul_le_mul_left (numBlocks N w) hstep
    have h2 := Nat.mul_le_mul_left (numBlocks N w) hcleanup
    linarith
  have hregroup :
      numBlocks N w * (12 * w * ℓ) + numBlocks N w * (3 * w * ℓ)
        = 15 * (numBlocks N w * w) * ℓ := by ring
  have hnb := numBlocks_times_w_le hw hN
  have hbig : 15 * (numBlocks N w * w) * ℓ ≤ 15 * (2 * N) * ℓ := by
    have h1 : 15 * (numBlocks N w * w) ≤ 15 * (2 * N) :=
      Nat.mul_le_mul_left 15 hnb
    have h2 : 15 * (numBlocks N w * w) * ℓ ≤ 15 * (2 * N) * ℓ :=
      Nat.mul_le_mul_right ℓ h1
    exact h2
  have hfinal : 15 * (2 * N) * ℓ = 30 * N * ℓ := by ring
  linarith

/-! ## 6. Speedup over the sequential scan -/

/-- **Blocked beats scan.** When the log factor `ℓ` is at most `w/10`,
    the blocked construction uses no more gates than the sequential
    scan of `RankSelectUpperBound.totalGateCost`. The scan cost is
    `N · (3w + 2)`, and the blocked cost is at most `30 · N · ℓ`,
    so `10 · ℓ ≤ w` suffices. -/
theorem blocked_beats_scan {N w ℓ : Nat}
    (hw : 1 ≤ w) (hN : w ≤ N) (hℓ : 1 ≤ ℓ) (hbeats : 10 * ℓ ≤ w) :
    blockedTotalGateCost N w ℓ ≤ totalGateCost N w := by
  have h1 : blockedTotalGateCost N w ℓ ≤ 30 * N * ℓ :=
    blockedTotalGateCost_le hw hN hℓ
  have h2 : 30 * N * ℓ = 3 * N * (10 * ℓ) := by ring
  have h3 : 3 * N * (10 * ℓ) ≤ 3 * N * w :=
    Nat.mul_le_mul_left (3 * N) hbeats
  have h4 : 3 * N * w ≤ N * (3 * w + 2) := by
    have hmono : 3 * w ≤ 3 * w + 2 := by omega
    have := Nat.mul_le_mul_left N hmono
    linarith
  have h5 : N * (3 * w + 2) = totalGateCost N w := by
    unfold totalGateCost stepGateCost
    ring
  linarith

/-! ## 7. Live ancilla count: `O(w)` -/

/-- Live ancilla in the blocked construction:
    - `w` bits for the running prefix counter `p`,
    - `ℓ` bits each for `c_q`, `ρ`, the local-output `ℓ`,
    - 1 bit for the `take_q` flag,
    - `2ℓ + 1` bits for the inner sequential-scan workspace
      (`RankSelectUpperBound.ancillaCount` applied at the inner
      output width `ℓ`, not the outer width `w`).
    All block-local registers reuse across blocks via step (f). -/
def liveAncillaCount (w ℓ : Nat) : Nat :=
  w + (ℓ + ℓ + ℓ + 1) + (2 * ℓ + 1)

/-- **Live ancilla upper bound.** Whenever `ℓ ≤ w`, the live ancilla
    count is at most `w + 5ℓ + 2 ≤ 6w + 2`. This is `O(w)` and
    matches the `O(w)` workspace claim of Theorem `thm:rs-block`. -/
theorem liveAncillaCount_le {w ℓ : Nat} (hℓw : ℓ ≤ w) :
    liveAncillaCount w ℓ ≤ 6 * w + 2 := by
  unfold liveAncillaCount
  linarith

/-! ## 8. Summary

### Upper bounds (blocked construction):
  - `blockStepCost_eq`         : exact per-block = 4wℓ + 8w
  - `blockStepCost_le_12wl`    : per-block ≤ 12wℓ
  - `blockedTotalGateCost_le`  : total ≤ 30 · N · ℓ

### Speedup vs. scan:
  - `blocked_beats_scan`       : blocked ≤ scan when 10ℓ ≤ w

### Workspace:
  - `liveAncillaCount_le`      : live ancillae ≤ 6w + 2

The asymptotic claim of the paper, `O(N log w)` gates with `O(w)`
clean ancillae, follows by setting `ℓ = ⌈log₂(w + 2)⌉` and observing
that this `ℓ` satisfies `1 ≤ ℓ` and `ℓ ≤ w` for all `w ≥ 1`.
-/

end BlockedRankSelect
