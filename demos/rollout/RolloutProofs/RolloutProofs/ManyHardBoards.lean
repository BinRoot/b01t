import RolloutProofs.BanditCore
import RolloutProofs.SwayDynamics
import RolloutProofs.MoveValues

/-!
# Many Hard Boards

Lifts the lower bound from a single witness board to an exponential family.

## Structure

1. `value_invariance_implies_hardness`: abstract transfer - if every board in
   a family shares the same move-value vector, ε-optimality transfers.

2. `colorVariantFamily`: the concrete exponential family - fix occupancy
   everywhere and fix cell states within the radius-H neighborhood of G,
   but vary colors freely on occupied exterior cells.

3. `family_moveValues_eq`: every board in the family has the same move-value
   vector, via `armMean_invariance` from `MoveValues.lean`.

4. `concrete_hardness_lifting`: the composed result - ε-optimality on the
   witness board implies ε-optimality on all 2^s boards in the family.

## Counting

If s exterior cells are occupied (occupancy frozen, colors free), the family
has 2^s members. This is exponential whenever s = Θ(m²).
-/

open Bandit
open SwayDynamics
open SwayMoveValues

noncomputable section

namespace SwayManyHardBoards

variable {m k : ℕ}

-- ════════════════════════════════════════════════════════════════
-- § 1: Abstract transfer
-- ════════════════════════════════════════════════════════════════

/-- If every board in a family has the same move-value vector as a witness
    board, then unique ε-optimality transfers from the witness to the
    entire family. -/
theorem value_invariance_implies_hardness
    (mv : Board m → BanditInstance k)
    (family : Set (Board m))
    (bStar : Board m)
    (eps : ℝ)
    (hinvar : ∀ b ∈ family, mv b = mv bStar)
    (i : Fin k)
    (hStar : IsEpsOptimal (mv bStar) eps i)
    :
    ∀ b ∈ family, IsEpsOptimal (mv b) eps i := by
  intro b hb
  rwa [hinvar b hb]

-- ════════════════════════════════════════════════════════════════
-- § 2: The color-variant family
-- ════════════════════════════════════════════════════════════════

/-- A board `b'` is a color variant of `bStar` with respect to witness
    region `G` and horizon `H` if:
    1. They agree on the radius-H neighborhood of G (cell states identical).
    2. Outside that neighborhood, they have the same occupancy pattern
       (same cells empty, same cells occupied - but colors may differ). -/
def colorVariantFamily
    (G : Finset (Pos m)) (H : ℕ) (bStar : Board m) : Set (Board m) :=
  { b' | (∀ x, gridDist_to_set x G ≤ H → b' x = bStar x) ∧
         (∀ x, ¬ (gridDist_to_set x G ≤ H) →
           (b' x = .empty ↔ bStar x = .empty)) }

/-- The witness board is in its own family. -/
theorem bStar_mem_family (G : Finset (Pos m)) (H : ℕ) (bStar : Board m) :
    bStar ∈ colorVariantFamily G H bStar := by
  refine ⟨fun _ _ => rfl, fun _ _ => Iff.rfl⟩

-- ════════════════════════════════════════════════════════════════
-- § 3: Move-value invariance via the concrete rollout bridge
-- ════════════════════════════════════════════════════════════════

/-- Every board in the color-variant family has the same move-value
    vector as the witness board. This follows directly from
    `armMean_invariance` in MoveValues.lean. -/
theorem family_moveValues_eq
    (firstMove : Fin k → Pos m) (G : Finset (Pos m)) (H : ℕ)
    (bStar : Board m) (b' : Board m)
    (hb' : b' ∈ colorVariantFamily G H bStar) :
    SwayMoveValues.moveValues (firstMove := firstMove) (G := G) b' H =
    SwayMoveValues.moveValues (firstMove := firstMove) (G := G) bStar H := by
  unfold SwayMoveValues.moveValues
  congr 1
  funext i
  exact armMean_invariance (firstMove := firstMove) (G := G)
    b' bStar H i hb'.1 hb'.2

-- ════════════════════════════════════════════════════════════════
-- § 4: Composed lifting theorem
-- ════════════════════════════════════════════════════════════════

/-- **Concrete hardness lifting.** If arm `i` is uniquely ε-optimal on a
    witness board `bStar`, then it is ε-optimal on every board in the
    exponential color-variant family. -/
theorem concrete_hardness_lifting
    (firstMove : Fin k → Pos m) (G : Finset (Pos m)) (H : ℕ)
    (bStar : Board m) (eps : ℝ) (i : Fin k)
    (hStar : IsEpsOptimal
      (SwayMoveValues.moveValues (firstMove := firstMove) (G := G) bStar H)
      eps i) :
    ∀ b ∈ colorVariantFamily G H bStar,
      IsEpsOptimal
        (SwayMoveValues.moveValues (firstMove := firstMove) (G := G) b H)
        eps i := by
  apply value_invariance_implies_hardness
    (mv := fun b => SwayMoveValues.moveValues (firstMove := firstMove) (G := G) b H)
    (family := colorVariantFamily G H bStar)
    (bStar := bStar)
  · intro b hb
    exact family_moveValues_eq firstMove G H bStar b hb
  · exact hStar

end SwayManyHardBoards
