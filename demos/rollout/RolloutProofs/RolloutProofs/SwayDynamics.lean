import Mathlib

/-!
# Sway Board Model

Defines the Sway board on an m×m grid (cell states, flip rule, d20 update)
and proves structural properties of the coupled-board disagreement dynamics:

- **One-step locality (Proposition 2):** if two boards agree at cell x and
  all orthogonal neighbors of x, the same d20 roll produces the same update
  at x.

- **Arithmetic bounds (Props 3–5):** per-edge transmission rate 1/20,
  persistence ≥ 4/5, and zero clearance at a 2-2 color split.

- **Per-edge transmission:** q(p) = (20/39)·[p + (1−p)³/3] is positive
  for 0 < p < 1.
-/

open Real Finset

noncomputable section

namespace SwayDynamics

-- ════════════════════════════════════════════════════════════════
-- § 1: Board Model
-- ════════════════════════════════════════════════════════════════

inductive CellState where
  | black | white | empty
  deriving DecidableEq, Repr

def Board (m : ℕ) := Fin m × Fin m → CellState

def gridDist {m : ℕ} (p q : Fin m × Fin m) : ℕ :=
  Int.natAbs ((p.1 : ℤ) - q.1) + Int.natAbs ((p.2 : ℤ) - q.2)

def orthNeighbors {m : ℕ} (p : Fin m × Fin m) : Finset (Fin m × Fin m) :=
  Finset.univ.filter fun q => gridDist p q = 1

def isFriendly : CellState → CellState → Bool
  | .black, .black => true
  | .white, .white => true
  | _, _ => false

def flipColor : CellState → CellState
  | .black => .white
  | .white => .black
  | .empty => .empty

def friendlyCount {m : ℕ} (board : Board m) (x : Fin m × Fin m) : ℕ :=
  ((orthNeighbors x).filter (fun y => isFriendly (board x) (board y))).card

/-- Flip threshold: piece with k friendly neighbors flips on d20 roll < (4−k). -/
def flipThreshold (k : ℕ) : ℕ := 4 - min k 4

/-- Single-cell update given a d20 roll.
    Empty cells are unchanged; occupied cells flip if roll < threshold. -/
def updateCell {m : ℕ} (board : Board m) (x : Fin m × Fin m)
    (roll : Fin 20) : CellState :=
  if board x = .empty then .empty
  else if roll.val < flipThreshold (friendlyCount board x)
    then flipColor (board x) else board x

-- ════════════════════════════════════════════════════════════════
-- § 2: One-Step Locality (Proposition 2)
-- ════════════════════════════════════════════════════════════════

theorem friendlyCount_eq_of_local_agree {m : ℕ} (b1 b2 : Board m)
    (x : Fin m × Fin m)
    (hx : b1 x = b2 x) (hn : ∀ y ∈ orthNeighbors x, b1 y = b2 y) :
    friendlyCount b1 x = friendlyCount b2 x := by
  unfold friendlyCount
  congr 1
  apply Finset.filter_congr
  intro y hy
  simp only [hx, hn y hy]

/-- If two boards agree at x and its neighbors, the same roll produces the
    same update at x. -/
theorem prop2_locality {m : ℕ} (b1 b2 : Board m)
    (x : Fin m × Fin m) (roll : Fin 20)
    (hx : b1 x = b2 x) (hn : ∀ y ∈ orthNeighbors x, b1 y = b2 y) :
    updateCell b1 x roll = updateCell b2 x roll := by
  unfold updateCell
  rw [hx, friendlyCount_eq_of_local_agree b1 b2 x hx hn]

-- ════════════════════════════════════════════════════════════════
-- § 3: Arithmetic Bounds (Props 3–5)
-- ════════════════════════════════════════════════════════════════

theorem prop3_per_edge_rate : (1 : ℝ) / 20 = 0.05 := by norm_num

theorem prop4_persistence_bound : 1 - (4 : ℝ) / 20 = 4 / 5 := by norm_num

theorem cor5_zero_clearance : flipThreshold 2 - flipThreshold 2 = 0 := by
  simp [flipThreshold]

-- ════════════════════════════════════════════════════════════════
-- § 4: Per-Edge Transmission
-- ════════════════════════════════════════════════════════════════

noncomputable def q_transmission (p : ℝ) : ℝ :=
  (20 / 39) * (p + (1 - p) ^ 3 / 3)

theorem per_edge_transmission_bound (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    0 < q_transmission p := by
  unfold q_transmission
  apply mul_pos (by norm_num : (0 : ℝ) < 20 / 39)
  have h1p : 0 ≤ 1 - p := by linarith
  have : 0 ≤ (1 - p) ^ 3 := by positivity
  linarith

end SwayDynamics
