import RigidificationCofBoundaryGlue

open CategoryTheory CategoryTheory.Limits MonoidalCategory HomotopicalAlgebra Opposite
open scoped Simplicial

universe u

namespace DaggerOrdinaryRigidificationCof.BoundaryData

noncomputable section

open PathFacets SimplicialThickening

variable {n : ℕ} {A B : SC.{u}}

theorem properMap_over (a : (SSet.boundary (n + 1)).toSSet ⟶ N.obj A)
    (b : SSet.stdSimplex.obj ⦋n + 1⦌ ⟶ N.obj B) (p : A ⟶ B)
    (sq : CommSq a (SSet.boundary (n + 1)).ι (N.map p) b)
    (i j : Fin (n + 2)) (hp : ¬ (i = 0 ∧ j = Fin.last (n + 1))) :
    properMap a i j hp ≫ p.map (vertex a i) (vertex a j) =
      (topWithVertices a b p sq).map (.mk (ULift.up i)) (.mk (ULift.up j)) := by
  by_cases hij : i ≤ j
  · simpa only [properMap, dif_pos hij] using forwardProperMap_over a b p sq i j hij hp
  · exact empty_hom_ext (show ULift.up.{u} j < ULift.up i from lt_of_not_ge hij) _ _

theorem faceEvaluation_over (a : (SSet.boundary (n + 1)).toSSet ⟶ N.obj A)
    (b : SSet.stdSimplex.obj ⦋n + 1⦌ ⟶ N.obj B) (p : A ⟶ B)
    (sq : CommSq a (SSet.boundary (n + 1)).ι (N.map p) b)
    (s : Finset (Fin (n + 2))) (hs : s.Nonempty) (hp : s ≠ Finset.univ)
    (i j : Fin (n + 2)) (hi : i ∈ s) (hj : j ∈ s) :
    faceEvaluation a s hs hp i j hi hj ≫ p.map (vertex a i) (vertex a j) =
      (pathsInFace s i j).ι ≫
        (topWithVertices a b p sq).map (.mk (ULift.up i)) (.mk (ULift.up j)) := by
  apply (cancel_epi (facePathsIso.{u} s i j hi hj).hom).mp
  change facePathMap s i j hi hj ≫ _ = facePathMap s i j hi hj ≫ _
  rw [← Category.assoc, facePathMap_evaluation, faceMap_over,
    ← Category.assoc, facePathMap_ι]

theorem omittedEvaluation_over (a : (SSet.boundary (n + 1)).toSSet ⟶ N.obj A)
    (b : SSet.stdSimplex.obj ⦋n + 1⦌ ⟶ N.obj B) (p : A ⟶ B)
    (sq : CommSq a (SSet.boundary (n + 1)).ι (N.map p) b) (k : interior n) :
    omittedEvaluation a k ≫ p.map (vertex a 0) (vertex a (Fin.last (n + 1))) =
      (extremeOmitted n k).ι ≫ (topWithVertices a b p sq).map
        (.mk (ULift.up 0)) (.mk (ULift.up (Fin.last (n + 1)))) := by
  unfold omittedEvaluation
  rw [Category.assoc, faceEvaluation_over, ← Category.assoc, SSet.Subcomplex.homOfLE_ι]

theorem cutEvaluation_over (a : (SSet.boundary (n + 1)).toSSet ⟶ N.obj A)
    (b : SSet.stdSimplex.obj ⦋n + 1⦌ ⟶ N.obj B) (p : A ⟶ B)
    (sq : CommSq a (SSet.boundary (n + 1)).ι (N.map p) b) (k : interior n) :
    cutEvaluation a k ≫ p.map (vertex a 0) (vertex a (Fin.last (n + 1))) =
      (extremeCut n k).ι ≫ (topWithVertices a b p sq).map
        (.mk (ULift.up 0)) (.mk (ULift.up (Fin.last (n + 1)))) := by
  apply (cancel_epi (cutIso (ULift.up 0) (ULift.up k.val)
    (ULift.up (Fin.last (n + 1)))).hom).mp
  change cutMap _ _ _ ≫ _ = cutMap _ _ _ ≫ _
  rw [← Category.assoc, cutMap_evaluation, Category.assoc, p.map_comp,
    ← Category.assoc, tensorHom_comp_tensorHom,
    properMap_over a b p sq, properMap_over a b p sq]
  have hk : cutMap (ULift.up 0) (ULift.up k.val) (ULift.up (Fin.last (n + 1))) ≫
      (extremeCut.{u} n k).ι =
      compose (ULift.up 0) (ULift.up k.val) (ULift.up (Fin.last (n + 1))) :=
    cutMap_ι _ _ _
  rw [← Category.assoc, hk]
  exact ((topWithVertices a b p sq).map_comp (.mk (ULift.up 0))
    (.mk (ULift.up k.val)) (.mk (ULift.up (Fin.last (n + 1))))).symm

/-- The SAME supplied square induces the actual scalar square, before choosing its lift. -/
def scalarSquare (a : (SSet.boundary (n + 1)).toSSet ⟶ N.obj A)
    (b : SSet.stdSimplex.obj ⦋n + 1⦌ ⟶ N.obj B) (p : A ⟶ B)
    (sq : CommSq a (SSet.boundary (n + 1)).ι (N.map p) b) :
    CommSq (boundaryMap a) (extremeBoundary.{u} n).ι
      (p.map (vertex a 0) (vertex a (Fin.last (n + 1))))
      ((topWithVertices a b p sq).map (.mk (ULift.up 0))
        (.mk (ULift.up (Fin.last (n + 1))))) := by
  constructor
  apply boundaryMap_hom_ext
  rintro (k | k)
  · rw [← Category.assoc, boundaryMap_restrict]
    change omittedEvaluation a k ≫ _ = _
    rw [omittedEvaluation_over a b p sq, ← Category.assoc, SSet.Subcomplex.homOfLE_ι]
    rfl
  · rw [← Category.assoc, boundaryMap_restrict]
    change cutEvaluation a k ≫ _ = _
    rw [cutEvaluation_over a b p sq, ← Category.assoc, SSet.Subcomplex.homOfLE_ι]
    rfl

def scalarLift (a : (SSet.boundary (n + 1)).toSSet ⟶ N.obj A)
    (b : SSet.stdSimplex.obj ⦋n + 1⦌ ⟶ N.obj B) (p : A ⟶ B)
    (sq : CommSq a (SSet.boundary (n + 1)).ι (N.map p) b)
    (hp : ordinaryTrivialFibrations p) : (scalarSquare a b p sq).LiftStruct := by
  letI := scalar_lifting (p.map (vertex a 0) (vertex a (Fin.last (n + 1))))
    (extremeBoundary.{u} n).ι (hp.2 _ _).1 (hp.2 _ _).2
  exact { l := (scalarSquare a b p sq).lift
          fac_left := (scalarSquare a b p sq).fac_left
          fac_right := (scalarSquare a b p sq).fac_right }

end

end DaggerOrdinaryRigidificationCof.BoundaryData
