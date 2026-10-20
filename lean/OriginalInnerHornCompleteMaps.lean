import OriginalInnerHornGlue
import RigidificationCofCompleteMaps

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open scoped Simplicial

universe u

namespace DaggerOrdinaryRigidificationCof.InnerHornCompleteMaps

noncomputable section

open BoundaryData PathFacets SimplicialThickening InnerHornFaces

variable {n : ℕ} {A : SC.{u}} (k : interior n)
variable (D : CompatibleFaceData (n + 1) A (Admissible k))
variable (ell : extremeHom.{u} n ⟶
  (D.obj 0 ⟶[SSet.{u}] D.obj (Fin.last (n + 1))))

/-- Supply the single missing extreme Hom map while keeping all admitted maps. -/
def completeMap (i j : Fin (n + 2)) :
    hom (ULift.up i) (ULift.up j) ⟶ (D.obj i ⟶[SSet.{u}] D.obj j) :=
  if h : i = 0 ∧ j = Fin.last (n + 1) then by
    rcases h with ⟨rfl, rfl⟩
    exact ell
  else InnerHornProperMaps.properMap k D i j h

theorem completeMap_proper (i j : Fin (n + 2))
    (hp : ¬ (i = 0 ∧ j = Fin.last (n + 1))) :
    completeMap k D ell i j = InnerHornProperMaps.properMap k D i j hp := by
  simp only [completeMap, dif_neg hp]

theorem completeMap_extreme :
    completeMap k D ell 0 (Fin.last (n + 1)) = ell := by
  unfold completeMap
  rw [dif_pos (show (0 : Fin (n + 2)) = 0 ∧
    Fin.last (n + 1) = Fin.last (n + 1) from ⟨rfl, rfl⟩)]

theorem completeMap_id (i : Fin (n + 2)) :
    eId SSet.{u} (SimplicialThickening.mk (ULift.up i)) ≫
      completeMap k D ell i i = eId SSet (D.obj i) := by
  rw [completeMap_proper k D ell i i (diagonal_proper i)]
  exact InnerHornProperMaps.properMap_id k D i

theorem completeMap_comp_left_unit (i j : Fin (n + 2)) :
    compose (ULift.up i) (ULift.up i) (ULift.up j) ≫ completeMap k D ell i j =
      (completeMap k D ell i i ⊗ₘ completeMap k D ell i j) ≫
        eComp SSet (D.obj i) (D.obj i) (D.obj j) := by
  apply NatTrans.ext
  funext q p
  rcases p with ⟨γ, δ⟩
  rw [diagonal_simplex (ULift.up i) q γ]
  have hs := element_id_comp (E := T.obj ⦋n + 1⦌)
    (x := .mk (ULift.up i)) (y := .mk (ULift.up j)) q δ
  have hi := congrFun (congrArg (fun f ↦ f.app q) (completeMap_id k D ell i)) PUnit.unit
  change (completeMap k D ell i i).app q
    ((eId SSet (.mk (ULift.up i) : (T.obj ⦋n + 1⦌).Obj)).app q PUnit.unit) =
      (eId SSet (D.obj i)).app q PUnit.unit at hi
  change (completeMap k D ell i j).app q
    ((compose (ULift.up i) (ULift.up i) (ULift.up j)).app q
      ((eId SSet (.mk (ULift.up i) : (T.obj ⦋n + 1⦌).Obj)).app q PUnit.unit, δ)) = _
  change (compose (ULift.up i) (ULift.up i) (ULift.up j)).app q
    ((eId SSet (.mk (ULift.up i) : (T.obj ⦋n + 1⦌).Obj)).app q PUnit.unit, δ) = δ at hs
  rw [hs]
  change _ = (eComp SSet (D.obj i) (D.obj i) (D.obj j)).app q
    ((completeMap k D ell i i).app q
      ((eId SSet (.mk (ULift.up i) : (T.obj ⦋n + 1⦌).Obj)).app q PUnit.unit),
        (completeMap k D ell i j).app q δ)
  rw [hi, element_id_comp]

theorem completeMap_comp_right_unit (i j : Fin (n + 2)) :
    compose (ULift.up i) (ULift.up j) (ULift.up j) ≫ completeMap k D ell i j =
      (completeMap k D ell i j ⊗ₘ completeMap k D ell j j) ≫
        eComp SSet (D.obj i) (D.obj j) (D.obj j) := by
  apply NatTrans.ext
  funext q p
  rcases p with ⟨γ, δ⟩
  rw [diagonal_simplex (ULift.up j) q δ]
  have hs := element_comp_id (E := T.obj ⦋n + 1⦌)
    (x := .mk (ULift.up i)) (y := .mk (ULift.up j)) q γ
  have hi := congrFun (congrArg (fun f ↦ f.app q) (completeMap_id k D ell j)) PUnit.unit
  change (completeMap k D ell j j).app q
    ((eId SSet (.mk (ULift.up j) : (T.obj ⦋n + 1⦌).Obj)).app q PUnit.unit) =
      (eId SSet (D.obj j)).app q PUnit.unit at hi
  change (completeMap k D ell i j).app q
    ((compose (ULift.up i) (ULift.up j) (ULift.up j)).app q
      (γ, (eId SSet (.mk (ULift.up j) : (T.obj ⦋n + 1⦌).Obj)).app q PUnit.unit)) = _
  change (compose (ULift.up i) (ULift.up j) (ULift.up j)).app q
    (γ, (eId SSet (.mk (ULift.up j) : (T.obj ⦋n + 1⦌).Obj)).app q PUnit.unit) = γ
      at hs
  rw [hs]
  change _ = (eComp SSet (D.obj i) (D.obj j) (D.obj j)).app q
    ((completeMap k D ell i j).app q γ, (completeMap k D ell j j).app q
      ((eId SSet (.mk (ULift.up j) : (T.obj ⦋n + 1⦌).Obj)).app q PUnit.unit))
  rw [hi, element_comp_id]

end

end DaggerOrdinaryRigidificationCof.InnerHornCompleteMaps
