import RolloutProofs.BanditCore
import RolloutProofs.SwayDynamics
import Mathlib.Tactic

/-!
# Move values and the rollout bridge

Explicit rollout semantics and the induced `k`-armed bandit instance.

- `terminalBoard` runs a fixed-horizon rollout from a board `b` after forcing
  a candidate first move `firstMove i`.
- Each later round performs:
  1. rank-based black placement among empty cells,
  2. rank-based white placement among empty cells,
  3. synchronous sway update via `updateCell`.
- `moveValues b H` is the resulting `k`-armed bandit instance whose means are
  the expected local terminal scores on `G`.
- `moveValues_invariance` is the peripheral-invariance theorem for that
  instance: agreement on the radius-`H` neighborhood of `G`, together with
  matching occupancy outside it, is enough to fix every arm mean.
-/

open BigOperators
open Bandit
open SwayDynamics

noncomputable section

namespace SwayMoveValues

abbrev Pos (m : ℕ) := Fin m × Fin m

/-- Distance from a cell to a finite witness region. Returns `0` for `∅`. -/
def gridDist_to_set {m : ℕ} (x : Pos m) (G : Finset (Pos m)) : ℕ :=
  if h : G.Nonempty then G.inf' h (fun y => gridDist x y) else 0

/-!
## Distance glue

These lemmas let us push `gridDist_to_set` bounds across one-step neighborhoods.
They are the only place we use triangle-style reasoning.
-/

theorem gridDist_comm {m : ℕ} (x y : Pos m) : gridDist x y = gridDist y x := by
  classical
  unfold gridDist
  have h1 : Int.natAbs ((x.1 : ℤ) - y.1) = Int.natAbs ((y.1 : ℤ) - x.1) := by
    have hsub : -((x.1 : ℤ) - y.1) = (y.1 : ℤ) - x.1 := by
      abel
    calc
      Int.natAbs ((x.1 : ℤ) - y.1)
          = Int.natAbs (-((x.1 : ℤ) - y.1)) := by
              simpa using (Int.natAbs_neg ((x.1 : ℤ) - y.1)).symm
      _ = Int.natAbs ((y.1 : ℤ) - x.1) := by
              simp [hsub]
  have h2 : Int.natAbs ((x.2 : ℤ) - y.2) = Int.natAbs ((y.2 : ℤ) - x.2) := by
    have hsub : -((x.2 : ℤ) - y.2) = (y.2 : ℤ) - x.2 := by
      abel
    calc
      Int.natAbs ((x.2 : ℤ) - y.2)
          = Int.natAbs (-((x.2 : ℤ) - y.2)) := by
              simpa using (Int.natAbs_neg ((x.2 : ℤ) - y.2)).symm
      _ = Int.natAbs ((y.2 : ℤ) - x.2) := by
              simp [hsub]
  simp [h1, h2]

theorem gridDist_triangle {m : ℕ} (x y z : Pos m) :
    gridDist x z ≤ gridDist x y + gridDist y z := by
  classical
  unfold gridDist
  have h1 :
      Int.natAbs ((x.1 : ℤ) - z.1) ≤
        Int.natAbs ((x.1 : ℤ) - y.1) + Int.natAbs ((y.1 : ℤ) - z.1) := by
    simpa [sub_add_sub_cancel] using
      (Int.natAbs_add_le ((x.1 : ℤ) - y.1) ((y.1 : ℤ) - z.1))
  have h2 :
      Int.natAbs ((x.2 : ℤ) - z.2) ≤
        Int.natAbs ((x.2 : ℤ) - y.2) + Int.natAbs ((y.2 : ℤ) - z.2) := by
    simpa [sub_add_sub_cancel] using
      (Int.natAbs_add_le ((x.2 : ℤ) - y.2) ((y.2 : ℤ) - z.2))
  have hsum := Nat.add_le_add h1 h2
  simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hsum

theorem gridDist_to_set_le_add {m : ℕ}
    (x y : Pos m) (G : Finset (Pos m)) :
    gridDist_to_set y G ≤ gridDist y x + gridDist_to_set x G := by
  classical
  by_cases hG : G.Nonempty
  · rcases Finset.exists_mem_eq_inf' (s := G) (H := hG) (f := fun z => gridDist x z) with
      ⟨z, hzG, hxz⟩
    have hxy_z : gridDist y z ≤ gridDist y x + gridDist x z :=
      gridDist_triangle (x := y) (y := x) (z := z)
    have hy_le : gridDist_to_set y G ≤ gridDist y z := by
      simpa [gridDist_to_set, hG] using
        (Finset.inf'_le (s := G) (f := fun w => gridDist y w) (h := hzG))
    have hx_eq : gridDist_to_set x G = gridDist x z := by
      simpa [gridDist_to_set, hG] using hxz
    calc
      gridDist_to_set y G
          ≤ gridDist y z := hy_le
      _ ≤ gridDist y x + gridDist x z := hxy_z
      _ = gridDist y x + gridDist_to_set x G := by simp [hx_eq]
  · simp [gridDist_to_set, hG]

theorem gridDist_to_set_neighbor {m : ℕ}
    (x y : Pos m) (G : Finset (Pos m)) (d : ℕ)
    (hx : gridDist_to_set x G ≤ d)
    (hxy : gridDist y x ≤ 1) :
    gridDist_to_set y G ≤ d + 1 := by
  have hle := gridDist_to_set_le_add (x := x) (y := y) G
  have hsum : gridDist y x + gridDist_to_set x G ≤ 1 + d :=
    Nat.add_le_add hxy hx
  have : gridDist_to_set y G ≤ 1 + d := le_trans hle hsum
  simpa [Nat.add_comm] using this

/-- Occupancy predicate. -/
def occupied : CellState → Prop
  | .empty => False
  | .black => True
  | .white => True

/-- Overwrite one board location. -/
def setCell {m : ℕ} (b : Board m) (x : Pos m) (c : CellState) : Board m :=
  fun y => if y = x then c else b y

/-- Place a stone if the chosen cell is empty; otherwise leave the board unchanged. -/
def placeAt {m : ℕ} (b : Board m) (x : Pos m) (c : CellState) : Board m :=
  if b x = .empty then setCell b x c else b

/-!
## Placement plumbing

`placeAt` only modifies the chosen location, and its emptiness behavior is simple enough to
package as reusable lemmas.
-/

theorem placeAt_self_of_empty {m : ℕ} (b : Board m) (p : Pos m) (c : CellState)
    (hp : b p = .empty) :
    placeAt b p c p = c := by
  unfold placeAt
  simp [hp, setCell]

theorem placeAt_self_of_not_empty {m : ℕ} (b : Board m) (p : Pos m) (c : CellState)
    (hp : b p ≠ .empty) :
    placeAt b p c p = b p := by
  unfold placeAt
  simp [hp]

theorem placeAt_of_ne {m : ℕ} (b : Board m) (p x : Pos m) (c : CellState)
    (hpx : x ≠ p) :
    placeAt b p c x = b x := by
  unfold placeAt
  by_cases hp : b p = .empty
  · simp [hp, setCell, hpx]
  · simp [hp]

theorem placeAt_preserves_agree {m : ℕ}
    (b b' : Board m) (p : Pos m) (c : CellState)
    (P : Pos m → Prop)
    (hagree : ∀ x, P x → b x = b' x) :
    ∀ x, P x → placeAt b p c x = placeAt b' p c x := by
  intro x hx
  by_cases hxp : x = p
  · subst x
    have hp : b p = b' p := hagree p hx
    by_cases hempty : b p = .empty
    · have hempty' : b' p = .empty := by simpa [hp] using hempty
      simp [placeAt, hempty, hempty', setCell]
    · have hempty' : b' p ≠ .empty := by
        intro h
        exact hempty (by simpa [hp] using h)
      simp [placeAt, hempty', hp]
  · have hpx : x ≠ p := hxp
    simp [placeAt_of_ne (b := b) (p := p) (x := x) (c := c) hpx,
      placeAt_of_ne (b := b') (p := p) (x := x) (c := c) hpx,
      hagree x hx]

theorem placeAt_preserves_empty_iff {m : ℕ}
    (b b' : Board m) (p : Pos m) (c : CellState)
    (hocc : ∀ x, b x = .empty ↔ b' x = .empty) :
    ∀ x, placeAt b p c x = .empty ↔ placeAt b' p c x = .empty := by
  intro x
  by_cases hxp : x = p
  · subst x
    by_cases hempty : b p = .empty
    · have hempty' : b' p = .empty := (hocc p).1 hempty
      simp [placeAt, hempty, hempty', setCell]
    · have hempty' : b' p ≠ .empty := by
        intro h
        exact hempty ((hocc p).2 h)
      simp [placeAt, hempty, hempty']
  · have hpx : x ≠ p := hxp
    simp [placeAt_of_ne (b := b) (p := p) (x := x) (c := c) hpx,
      placeAt_of_ne (b := b') (p := p) (x := x) (c := c) hpx,
      hocc x]

/-- Place at an optional selected location. -/
def placeOpt {m : ℕ} (b : Board m) (x? : Option (Pos m)) (c : CellState) : Board m :=
  match x? with
  | none => b
  | some x => placeAt b x c

theorem placeOpt_preserves_agree {m : ℕ}
    (b b' : Board m) (x? : Option (Pos m)) (c : CellState)
    (P : Pos m → Prop)
    (hagree : ∀ x, P x → b x = b' x) :
    ∀ x, P x → placeOpt b x? c x = placeOpt b' x? c x := by
  intro x hx
  cases x? with
  | none => simp [placeOpt, hagree x hx]
  | some p =>
    simpa [placeOpt] using placeAt_preserves_agree (b := b) (b' := b') (p := p) (c := c)
      (P := P) hagree x hx

theorem placeOpt_preserves_empty_iff {m : ℕ}
    (b b' : Board m) (x? : Option (Pos m)) (c : CellState)
    (hocc : ∀ x, b x = .empty ↔ b' x = .empty) :
    ∀ x, placeOpt b x? c x = .empty ↔ placeOpt b' x? c x = .empty := by
  intro x
  cases x? with
  | none => simp [placeOpt, hocc x]
  | some p =>
    simpa [placeOpt] using placeAt_preserves_empty_iff (b := b) (b' := b') (p := p) (c := c) hocc x

/-- Single-cell occupancy preservation for the already-defined local Sway update. -/
theorem updateCell_empty_iff {m : ℕ} (b : Board m) (x : Pos m) (roll : Fin 20) :
    updateCell b x roll = .empty ↔ b x = .empty := by
  unfold updateCell
  by_cases hx : b x = .empty
  · simp [hx]
  · rw [if_neg hx]
    cases hbx : b x with
    | empty => cases hx (by simp [hbx])
    | black =>
      by_cases hroll : roll.val < flipThreshold (friendlyCount b x)
      · simp [hroll, flipColor]
      · simp [hroll]
    | white =>
      by_cases hroll : roll.val < flipThreshold (friendlyCount b x)
      · simp [hroll, flipColor]
      · simp [hroll]

theorem updateCell_preserves_occupancy {m : ℕ} (b : Board m) (x : Pos m) (roll : Fin 20) :
    occupied (updateCell b x roll) ↔ occupied (b x) := by
  cases hbx : b x with
  | empty =>
    simp [occupied, updateCell, hbx]
  | black =>
    by_cases hroll : roll.val < flipThreshold (friendlyCount b x)
    · simp [occupied, updateCell, hbx, hroll, flipColor]
    · simp [occupied, updateCell, hbx, hroll]
  | white =>
    by_cases hroll : roll.val < flipThreshold (friendlyCount b x)
    · simp [occupied, updateCell, hbx, hroll, flipColor]
    · simp [occupied, updateCell, hbx, hroll]

/-- Synchronous sway update for one full dice field. -/
def swayStep {m : ℕ} (b : Board m) (ρ : Pos m → Fin 20) : Board m :=
  fun x => updateCell b x (ρ x)

/-- Sway preserves occupancy pointwise. -/
theorem swayStep_empty_iff {m : ℕ} (b : Board m) (ρ : Pos m → Fin 20) (x : Pos m) :
    swayStep b ρ x = .empty ↔ b x = .empty := by
  unfold swayStep
  exact updateCell_empty_iff b x (ρ x)

theorem swayStep_eq_of_ball_agree {m : ℕ}
    (b b' : Board m) (ρ : Pos m → Fin 20) (x : Pos m)
    (hball : ∀ y, gridDist y x ≤ 1 → b y = b' y) :
    swayStep b ρ x = swayStep b' ρ x := by
  unfold swayStep
  -- `prop2_locality` needs equality at `x` and at all orthogonal neighbors.
  refine prop2_locality b b' x (ρ x) ?_ ?_
  · exact hball x (by simp [gridDist])
  · intro y hy
    have hy' : y ∈ (orthNeighbors x) := hy
    have hdistxy : gridDist x y = 1 := by
      have : y ∈ Finset.univ.filter (fun q => gridDist x q = 1) := by
        simpa [orthNeighbors] using hy'
      exact (Finset.mem_filter.1 this).2
    have hdistyx : gridDist y x ≤ 1 := by
      have : gridDist y x = 1 := by
        have hcomm : gridDist y x = gridDist x y := by
          simpa using (gridDist_comm (x := y) (y := x))
        simpa [hcomm] using hdistxy
      simp [this]
    exact hball y hdistyx

/-- Canonical row-major list of all positions. -/
def allPositions (m : ℕ) : List (Pos m) :=
  (List.finRange m).flatMap fun i => (List.finRange m).map fun j => (i, j)

/-- Empty cells in row-major order. -/
def emptyPositions {m : ℕ} (b : Board m) : List (Pos m) :=
  (allPositions m).filter fun x => b x = .empty

theorem emptyPositions_eq_of_empty_iff {m : ℕ}
    (b b' : Board m)
    (hocc : ∀ x, b x = .empty ↔ b' x = .empty) :
    emptyPositions b = emptyPositions b' := by
  classical
  unfold emptyPositions
  refine List.filter_congr (l := allPositions m) ?_
  intro x _hx
  -- `List.filter` uses a Bool predicate; the Prop predicate is coerced via `decide`.
  have : decide (b x = CellState.empty) = decide (b' x = CellState.empty) := by
    exact (decide_eq_decide (p := b x = CellState.empty) (q := b' x = CellState.empty)).2 (hocc x)
  simpa using this

/-- Rank-select an empty cell in row-major order. Out-of-range selectors yield `none`. -/
def selectRankedEmpty? {m : ℕ} (b : Board m) (r : Fin (m * m + 1)) : Option (Pos m) :=
  (emptyPositions b)[r.val]?

theorem selectRankedEmpty?_eq_of_empty_iff {m : ℕ}
    (b b' : Board m) (r : Fin (m * m + 1))
    (hocc : ∀ x, b x = .empty ↔ b' x = .empty) :
    selectRankedEmpty? b r = selectRankedEmpty? b' r := by
  unfold selectRankedEmpty?
  simp [emptyPositions_eq_of_empty_iff (b := b) (b' := b') hocc]

/-- One complete later rollout round: black place, white place, sway update. -/
def rolloutRound {m : ℕ}
    (b : Board m)
    (rBlack rWhite : Fin (m * m + 1))
    (ρ : Pos m → Fin 20) : Board m :=
  let b1 := placeOpt b (selectRankedEmpty? b rBlack) .black
  let b2 := placeOpt b1 (selectRankedEmpty? b1 rWhite) .white
  swayStep b2 ρ

/-!
## One-round invariance

This is the heart of the rollout invariance proof: selector equality from global occupancy,
placements preserve agreement/occupancy, and sway locality shrinks the radius by one.
-/

theorem rolloutRound_invariant {m : ℕ}
    (b b' : Board m) (G : Finset (Pos m)) (d : ℕ)
    (rB rW : Fin (m * m + 1)) (ρ : Pos m → Fin 20)
    (hagree : ∀ x, gridDist_to_set x G ≤ d + 1 → b x = b' x)
    (hocc : ∀ x, b x = .empty ↔ b' x = .empty) :
    (∀ x, gridDist_to_set x G ≤ d →
      rolloutRound b rB rW ρ x = rolloutRound b' rB rW ρ x) ∧
    (∀ x, rolloutRound b rB rW ρ x = .empty ↔
          rolloutRound b' rB rW ρ x = .empty) := by
  classical
  -- black selector agrees
  have hselB : selectRankedEmpty? b rB = selectRankedEmpty? b' rB :=
    selectRankedEmpty?_eq_of_empty_iff (b := b) (b' := b') rB hocc
  set pB? : Option (Pos m) := selectRankedEmpty? b rB with hpB
  have hpB' : selectRankedEmpty? b' rB = pB? := by
    have : pB? = selectRankedEmpty? b' rB := by simpa [hpB] using hselB
    simpa using this.symm
  let b1 : Board m := placeOpt b pB? .black
  let b1' : Board m := placeOpt b' pB? .black
  have hagree1 : ∀ x, gridDist_to_set x G ≤ d + 1 → b1 x = b1' x := by
    intro x hx
    simpa [b1, b1'] using
      placeOpt_preserves_agree (b := b) (b' := b') (x? := pB?) (c := .black)
        (P := fun x => gridDist_to_set x G ≤ d + 1) hagree x hx
  have hocc1 : ∀ x, b1 x = .empty ↔ b1' x = .empty := by
    intro x
    simpa [b1, b1'] using
      placeOpt_preserves_empty_iff (b := b) (b' := b') (x? := pB?) (c := .black) hocc x
  -- white selector agrees (needs global occupancy equivalence on `b1/b1'`)
  have hselW : selectRankedEmpty? b1 rW = selectRankedEmpty? b1' rW :=
    selectRankedEmpty?_eq_of_empty_iff (b := b1) (b' := b1') rW hocc1
  set pW? : Option (Pos m) := selectRankedEmpty? b1 rW with hpW
  have hpW' : selectRankedEmpty? b1' rW = pW? := by
    have : pW? = selectRankedEmpty? b1' rW := by simpa [hpW] using hselW
    simpa using this.symm
  let b2 : Board m := placeOpt b1 pW? .white
  let b2' : Board m := placeOpt b1' pW? .white
  have hagree2 : ∀ x, gridDist_to_set x G ≤ d + 1 → b2 x = b2' x := by
    intro x hx
    simpa [b2, b2'] using
      placeOpt_preserves_agree (b := b1) (b' := b1') (x? := pW?) (c := .white)
        (P := fun x => gridDist_to_set x G ≤ d + 1) hagree1 x hx
  have hocc2 : ∀ x, b2 x = .empty ↔ b2' x = .empty := by
    intro x
    simpa [b2, b2'] using
      placeOpt_preserves_empty_iff (b := b1) (b' := b1') (x? := pW?) (c := .white) hocc1 x
  -- pointwise agreement on the next (shrunk) radius uses sway locality
  have hagreeRound : ∀ x, gridDist_to_set x G ≤ d →
      swayStep b2 ρ x = swayStep b2' ρ x := by
    intro x hx
    have hball : ∀ y, gridDist y x ≤ 1 → b2 y = b2' y := by
      intro y hy
      have hyG : gridDist_to_set y G ≤ d + 1 :=
        gridDist_to_set_neighbor (x := x) (y := y) (G := G) (d := d) hx hy
      exact hagree2 y hyG
    exact swayStep_eq_of_ball_agree (b := b2) (b' := b2') ρ x hball
  have hoccRound : ∀ x, swayStep b2 ρ x = .empty ↔ swayStep b2' ρ x = .empty := by
    intro x
    simpa [swayStep_empty_iff] using (hocc2 x)
  refine ⟨?_, ?_⟩
  · intro x hx
    simpa [rolloutRound, b1, b1', b2, b2', hpB.symm, hpB', hpW.symm, hpW'] using hagreeRound x hx
  · intro x
    simpa [rolloutRound, b1, b1', b2, b2', hpB.symm, hpB', hpW.symm, hpW'] using hoccRound x

/-- Finite randomness for later rounds: one black-rank and one white-rank per round. -/
abbrev SelectorStream (m : ℕ) (H : ℕ) :=
  Fin H → (Fin (m * m + 1) × Fin (m * m + 1))

/-- Finite randomness for later rounds: a d20 roll for each cell in each round. -/
abbrev RollStream (m : ℕ) (H : ℕ) := Fin H → Pos m → Fin 20

variable {m k : ℕ}
variable (firstMove : Fin k → Pos m)

/-- Fixed-horizon terminal board after forcing candidate arm `i` first. -/
def terminalBoard
    (b : Board m)
    (H : ℕ)
    (i : Fin k)
    (σ : SelectorStream m H)
    (ρ : RollStream m H) : Board m :=
  (List.finRange H).foldl
    (fun state t => rolloutRound state (σ t).1 (σ t).2 (ρ t))
    (placeAt b (firstMove i) .black)

/-- Local black count on `G`. -/
def localBlackCount (G : Finset (Pos m)) (b : Board m) : ℕ :=
  (G.filter fun x => b x = .black).card

/-- Local white count on `G`. -/
def localWhiteCount (G : Finset (Pos m)) (b : Board m) : ℕ :=
  (G.filter fun x => b x = .white).card

/-- Local terminal score: black-minus-white count on `G`. -/
def localScore (G : Finset (Pos m)) (b : Board m) : ℝ :=
  (localBlackCount G b : ℝ) - (localWhiteCount G b : ℝ)

theorem localScore_eq_of_agree_on_G
    (G : Finset (Pos m)) (b b' : Board m)
    (hagree : ∀ x ∈ G, b x = b' x) :
    localScore G b = localScore G b' := by
  have hblack :
      G.filter (fun x => b x = .black) = G.filter (fun x => b' x = .black) := by
    ext x
    by_cases hx : x ∈ G
    · simp [hx, hagree x hx]
    · simp [hx]
  have hwhite :
      G.filter (fun x => b x = .white) = G.filter (fun x => b' x = .white) := by
    ext x
    by_cases hx : x ∈ G
    · simp [hx, hagree x hx]
    · simp [hx]
  unfold localScore localBlackCount localWhiteCount
  rw [hblack, hwhite]

/-- Uniform average over a finite type. -/
def avgFintype {α : Type} [Fintype α] (f : α → ℝ) : ℝ :=
  ((∑ a, f a) : ℝ) / (Fintype.card α : ℝ)

theorem avgFintype_congr {α : Type} [Fintype α] (f g : α → ℝ)
    (hfg : ∀ a, f a = g a) :
    avgFintype f = avgFintype g := by
  unfold avgFintype
  simp [hfg]

variable (G : Finset (Pos m))

/-- Terminal score of a fixed rollout branch. -/
def rolloutScore
    (b : Board m) (H : ℕ) (i : Fin k)
    (σ : SelectorStream m H) (ρ : RollStream m H) : ℝ :=
  localScore G (terminalBoard (firstMove := firstMove) b H i σ ρ)

/-- Mean value of arm `i` under uniform averaging over later selector values and rolls. -/
def armMean (b : Board m) (H : ℕ) (i : Fin k) : ℝ :=
  avgFintype fun σ : SelectorStream m H =>
    avgFintype fun ρ : RollStream m H =>
      rolloutScore (firstMove := firstMove) (G := G) b H i σ ρ

/-- The rollout-value vector over the `k` candidate first moves. -/
def moveValues (b : Board m) (H : ℕ) : BanditInstance k :=
  ⟨fun i => armMean (firstMove := firstMove) (G := G) b H i⟩

/-!
## Rollout invariance

`H`-step induction on the fold implementing `terminalBoard`. The one-step
invariant pairs agreement on `N_d(G)` with global occupancy equality, so that
selectors stay synchronized while the agreement radius shrinks by one each
round.
-/

/--
If two initial boards agree on the radius-`H` neighborhood of `G` and have the
same occupancy pattern outside that neighborhood, then every fixed rollout
branch lands in terminal boards agreeing on `G`.
-/
theorem rollout_terminal_agree_on_G
    (b b' : Board m) (H : ℕ) (i : Fin k)
    (σ : SelectorStream m H) (ρ : RollStream m H)
    (hagree : ∀ x, gridDist_to_set x G ≤ H → b x = b' x)
    (hocc : ∀ x, ¬ (gridDist_to_set x G ≤ H) →
      (b x = .empty ↔ b' x = .empty))
    :
    ∀ x ∈ G,
      terminalBoard (firstMove := firstMove) b H i σ ρ x =
      terminalBoard (firstMove := firstMove) b' H i σ ρ x
    := by
  classical
  -- Upgrade the "outside only" occupancy hypothesis to global occupancy equivalence
  -- using agreement on the radius-`H` neighborhood.
  have hocc0 : ∀ x, b x = .empty ↔ b' x = .empty := by
    intro x
    by_cases hx : gridDist_to_set x G ≤ H
    · have hxb : b x = b' x := hagree x hx
      simp [hxb]
    · exact hocc x hx
  -- First forced move.
  set p : Pos m := firstMove i
  let b0 : Board m := placeAt b p .black
  let b0' : Board m := placeAt b' p .black
  have hagree0 : ∀ x, gridDist_to_set x G ≤ H → b0 x = b0' x := by
    intro x hx
    simpa [b0, b0'] using
      placeAt_preserves_agree (b := b) (b' := b') (p := p) (c := .black)
        (P := fun x => gridDist_to_set x G ≤ H) hagree x hx
  have hocc0' : ∀ x, b0 x = .empty ↔ b0' x = .empty := by
    intro x
    simpa [b0, b0'] using
      placeAt_preserves_empty_iff (b := b) (b' := b') (p := p) (c := .black) hocc0 x
  -- General fold lemma: each later round shrinks the agreement radius by one, while preserving
  -- global occupancy equivalence.
  have fold_invariant :
      ∀ (ts : List (Fin H)) (b₁ b₁' : Board m) (d : ℕ),
        (∀ x, gridDist_to_set x G ≤ d + ts.length → b₁ x = b₁' x) →
        (∀ x, b₁ x = .empty ↔ b₁' x = .empty) →
        let bt :=
          ts.foldl (fun state t => rolloutRound state (σ t).1 (σ t).2 (ρ t)) b₁
        let bt' :=
          ts.foldl (fun state t => rolloutRound state (σ t).1 (σ t).2 (ρ t)) b₁'
        (∀ x, gridDist_to_set x G ≤ d → bt x = bt' x) ∧
        (∀ x, bt x = .empty ↔ bt' x = .empty) := by
    intro ts
    induction ts with
    | nil =>
      intro b₁ b₁' d hagree₁ hocc₁ bt bt'
      refine ⟨?_, ?_⟩
      · intro x hx
        simpa using hagree₁ x (by simpa using hx)
      · intro x
        simpa using hocc₁ x
    | cons t ts ih =>
      intro b₁ b₁' d hagree₁ hocc₁ bt bt'
      have hstep := rolloutRound_invariant (b := b₁) (b' := b₁') (G := G) (d := d + ts.length)
        (rB := (σ t).1) (rW := (σ t).2) (ρ := ρ t) ?_ hocc₁
      · have hagree2 : ∀ x, gridDist_to_set x G ≤ d + ts.length →
            rolloutRound b₁ (σ t).1 (σ t).2 (ρ t) x =
            rolloutRound b₁' (σ t).1 (σ t).2 (ρ t) x := by
          intro x hx
          exact (hstep.1 x hx)
        have hocc2 : ∀ x,
            rolloutRound b₁ (σ t).1 (σ t).2 (ρ t) x = .empty ↔
            rolloutRound b₁' (σ t).1 (σ t).2 (ρ t) x = .empty :=
          hstep.2
        simpa [List.foldl] using
          ih (b₁ := rolloutRound b₁ (σ t).1 (σ t).2 (ρ t))
            (b₁' := rolloutRound b₁' (σ t).1 (σ t).2 (ρ t))
            (d := d) hagree2 hocc2
      · -- the one-step lemma takes radius `d + (t :: ts).length`; rewrite from `d + ts.length`
        intro x hx
        have hx' : gridDist_to_set x G ≤ d + (t :: ts).length := by
          simpa [List.length, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hx
        exact hagree₁ x hx'
  -- Apply the fold invariant to the full `H`-step finRange list at `d = 0`.
  have hfin :
      let bt :=
        (List.finRange H).foldl (fun state t => rolloutRound state (σ t).1 (σ t).2 (ρ t)) b0
      let bt' :=
        (List.finRange H).foldl (fun state t => rolloutRound state (σ t).1 (σ t).2 (ρ t)) b0'
      (∀ x, gridDist_to_set x G ≤ 0 → bt x = bt' x) ∧
      (∀ x, bt x = .empty ↔ bt' x = .empty) := by
    have hlen : (List.finRange H).length = H := by simp
    have hagreeH : ∀ x, gridDist_to_set x G ≤ 0 + (List.finRange H).length → b0 x = b0' x := by
      intro x hx
      have : gridDist_to_set x G ≤ H := by simpa [hlen] using hx
      exact hagree0 x this
    simpa using
      fold_invariant (ts := List.finRange H) (b₁ := b0) (b₁' := b0') (d := 0) hagreeH hocc0'
  intro x hxG
  have hx0 : gridDist_to_set x G ≤ 0 := by
    by_cases hG : G.Nonempty
    · have hinf : gridDist_to_set x G ≤ gridDist x x := by
        simpa [gridDist_to_set, hG] using
          (Finset.inf'_le (s := G) (f := fun y => gridDist x y) (h := hxG))
      exact le_trans hinf (by simp [gridDist])
    · cases (hG ⟨x, hxG⟩)
  have := hfin
  simpa [terminalBoard, b0, b0'] using (this.1 x hx0)

theorem rolloutScore_invariance
    (b b' : Board m) (H : ℕ) (i : Fin k)
    (σ : SelectorStream m H) (ρ : RollStream m H)
    (hagree : ∀ x, gridDist_to_set x G ≤ H → b x = b' x)
    (hocc : ∀ x, ¬ (gridDist_to_set x G ≤ H) →
      (b x = .empty ↔ b' x = .empty))
    :
    rolloutScore (firstMove := firstMove) (G := G) b H i σ ρ =
    rolloutScore (firstMove := firstMove) (G := G) b' H i σ ρ := by
  unfold rolloutScore
  apply localScore_eq_of_agree_on_G
  exact rollout_terminal_agree_on_G (firstMove := firstMove) (G := G)
    b b' H i σ ρ hagree hocc

theorem armMean_invariance
    (b b' : Board m) (H : ℕ) (i : Fin k)
    (hagree : ∀ x, gridDist_to_set x G ≤ H → b x = b' x)
    (hocc : ∀ x, ¬ (gridDist_to_set x G ≤ H) →
      (b x = .empty ↔ b' x = .empty))
    :
    armMean (firstMove := firstMove) (G := G) b H i =
    armMean (firstMove := firstMove) (G := G) b' H i := by
  unfold armMean
  apply avgFintype_congr
  intro σ
  apply avgFintype_congr
  intro ρ
  exact rolloutScore_invariance (firstMove := firstMove) (G := G)
    b b' H i σ ρ hagree hocc

theorem moveValues_invariance
    (b b' : Board m) (H : ℕ)
    (hagree : ∀ x, gridDist_to_set x G ≤ H → b x = b' x)
    (hocc : ∀ x, ¬ (gridDist_to_set x G ≤ H) →
      (b x = .empty ↔ b' x = .empty))
    :
    moveValues (firstMove := firstMove) (G := G) b H =
    moveValues (firstMove := firstMove) (G := G) b' H := by
  unfold moveValues
  congr
  funext i
  exact armMean_invariance (firstMove := firstMove) (G := G) b b' H i hagree hocc

end SwayMoveValues
