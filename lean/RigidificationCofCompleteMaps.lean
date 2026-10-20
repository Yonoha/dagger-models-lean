import RigidificationCofBoundaryGlue

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open scoped Simplicial

universe u

namespace DaggerOrdinaryRigidificationCof.BoundaryData

noncomputable section

open PathFacets SimplicialThickening

variable {n : ℕ} {A : SC.{u}}

def completeMap (a : (SSet.boundary (n + 1)).toSSet ⟶ N.obj A)
    (ell : extremeHom.{u} n ⟶ (vertex a 0 ⟶[SSet.{u}] vertex a (Fin.last (n + 1))))
    (i j : Fin (n + 2)) :
    hom (ULift.up i) (ULift.up j) ⟶ (vertex a i ⟶[SSet.{u}] vertex a j) :=
  if h : i = 0 ∧ j = Fin.last (n + 1) then by
    rcases h with ⟨rfl, rfl⟩
    exact ell
  else properMap a i j h

theorem completeMap_proper (a : (SSet.boundary (n + 1)).toSSet ⟶ N.obj A)
    (ell : extremeHom.{u} n ⟶ (vertex a 0 ⟶[SSet.{u}] vertex a (Fin.last (n + 1))))
    (i j : Fin (n + 2)) (hp : ¬ (i = 0 ∧ j = Fin.last (n + 1))) :
    completeMap a ell i j = properMap a i j hp := by simp only [completeMap, dif_neg hp]

theorem completeMap_extreme (a : (SSet.boundary (n + 1)).toSSet ⟶ N.obj A)
    (ell : extremeHom.{u} n ⟶ (vertex a 0 ⟶[SSet.{u}] vertex a (Fin.last (n + 1)))) :
    completeMap a ell 0 (Fin.last (n + 1)) = ell := by
  unfold completeMap
  rw [dif_pos (show (0 : Fin (n + 2)) = 0 ∧
    Fin.last (n + 1) = Fin.last (n + 1) from ⟨rfl, rfl⟩)]

theorem completeMap_id (a : (SSet.boundary (n + 1)).toSSet ⟶ N.obj A)
    (ell : extremeHom.{u} n ⟶ (vertex a 0 ⟶[SSet.{u}] vertex a (Fin.last (n + 1))))
    (i : Fin (n + 2)) :
    eId SSet.{u} (SimplicialThickening.mk (ULift.up i)) ≫ completeMap a ell i i =
      eId SSet (vertex a i) := by
  rw [completeMap_proper a ell i i (diagonal_proper i)]
  exact properMap_id a i

theorem element_id_comp {E : SC.{u}} {x y : E.Obj} (q : SimplexCategoryᵒᵖ)
    (g : (x ⟶[SSet.{u}] y).obj q) :
    (eComp SSet x x y).app q ((eId SSet x).app q PUnit.unit, g) = g :=
  congrFun (congrArg (fun f => f.app q) (e_id_comp SSet x y)) g

theorem element_comp_id {E : SC.{u}} {x y : E.Obj} (q : SimplexCategoryᵒᵖ)
    (g : (x ⟶[SSet.{u}] y).obj q) :
    (eComp SSet x y y).app q (g, (eId SSet y).app q PUnit.unit) = g :=
  congrFun (congrArg (fun f => f.app q) (e_comp_id SSet x y)) g

theorem completeMap_comp_left_unit
    (a : (SSet.boundary (n + 1)).toSSet ⟶ N.obj A)
    (ell : extremeHom.{u} n ⟶ (vertex a 0 ⟶[SSet.{u}] vertex a (Fin.last (n + 1))))
    (i j : Fin (n + 2)) :
    compose (ULift.up i) (ULift.up i) (ULift.up j) ≫ completeMap a ell i j =
      (completeMap a ell i i ⊗ₘ completeMap a ell i j) ≫
        eComp SSet (vertex a i) (vertex a i) (vertex a j) := by
  apply NatTrans.ext
  funext q p
  rcases p with ⟨γ, δ⟩
  rw [diagonal_simplex (ULift.up i) q γ]
  have hs := element_id_comp (E := T.obj ⦋n + 1⦌)
    (x := .mk (ULift.up i)) (y := .mk (ULift.up j)) q δ
  have hi := congrFun (congrArg (fun f => f.app q) (completeMap_id a ell i)) PUnit.unit
  change (completeMap a ell i i).app q
    ((eId SSet (.mk (ULift.up i) : (T.obj ⦋n + 1⦌).Obj)).app q PUnit.unit) =
      (eId SSet (vertex a i)).app q PUnit.unit at hi
  change (completeMap a ell i j).app q
    ((compose (ULift.up i) (ULift.up i) (ULift.up j)).app q
      ((eId SSet (.mk (ULift.up i) : (T.obj ⦋n + 1⦌).Obj)).app q PUnit.unit, δ)) = _
  change (compose (ULift.up i) (ULift.up i) (ULift.up j)).app q
    ((eId SSet (.mk (ULift.up i) : (T.obj ⦋n + 1⦌).Obj)).app q PUnit.unit, δ) = δ at hs
  rw [hs]
  change _ = (eComp SSet (vertex a i) (vertex a i) (vertex a j)).app q
    ((completeMap a ell i i).app q
      ((eId SSet (.mk (ULift.up i) : (T.obj ⦋n + 1⦌).Obj)).app q PUnit.unit),
        (completeMap a ell i j).app q δ)
  rw [hi, element_id_comp]

theorem completeMap_comp_right_unit
    (a : (SSet.boundary (n + 1)).toSSet ⟶ N.obj A)
    (ell : extremeHom.{u} n ⟶ (vertex a 0 ⟶[SSet.{u}] vertex a (Fin.last (n + 1))))
    (i j : Fin (n + 2)) :
    compose (ULift.up i) (ULift.up j) (ULift.up j) ≫ completeMap a ell i j =
      (completeMap a ell i j ⊗ₘ completeMap a ell j j) ≫
        eComp SSet (vertex a i) (vertex a j) (vertex a j) := by
  apply NatTrans.ext
  funext q p
  rcases p with ⟨γ, δ⟩
  rw [diagonal_simplex (ULift.up j) q δ]
  have hs := element_comp_id (E := T.obj ⦋n + 1⦌)
    (x := .mk (ULift.up i)) (y := .mk (ULift.up j)) q γ
  have hi := congrFun (congrArg (fun f => f.app q) (completeMap_id a ell j)) PUnit.unit
  change (completeMap a ell j j).app q
    ((eId SSet (.mk (ULift.up j) : (T.obj ⦋n + 1⦌).Obj)).app q PUnit.unit) =
      (eId SSet (vertex a j)).app q PUnit.unit at hi
  change (completeMap a ell i j).app q
    ((compose (ULift.up i) (ULift.up j) (ULift.up j)).app q
      (γ, (eId SSet (.mk (ULift.up j) : (T.obj ⦋n + 1⦌).Obj)).app q PUnit.unit)) = _
  change (compose (ULift.up i) (ULift.up j) (ULift.up j)).app q
    (γ, (eId SSet (.mk (ULift.up j) : (T.obj ⦋n + 1⦌).Obj)).app q PUnit.unit) = γ at hs
  rw [hs]
  change _ = (eComp SSet (vertex a i) (vertex a j) (vertex a j)).app q
    ((completeMap a ell i j).app q γ, (completeMap a ell j j).app q
      ((eId SSet (.mk (ULift.up j) : (T.obj ⦋n + 1⦌).Obj)).app q PUnit.unit))
  rw [hi, element_comp_id]

end

end DaggerOrdinaryRigidificationCof.BoundaryData
