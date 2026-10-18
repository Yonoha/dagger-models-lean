import ActualWalkingIsoCategoricalCylinder
import OriginalNerveOppositeMap

/-!
# Endpoint-preserving reversal of the original categorical interval

Use the already verified comparison from the reversed nerve to the nerve of the
opposite category. The unique arrows of the literal walking category identify
its opposite with itself while retaining both original objects.
-/
set_option autoImplicit false
open CategoryTheory Opposite Simplicial DaggerModels
open DaggerModels.OriginalWalkingIsoIntegerObstruction
open DaggerActualFreeWalkingIsoIntegerObstruction
open DaggerActualWalkingIsoCategoricalCylinder
open DaggerOriginalNerveOppositeMap
universe u
namespace DaggerActualWalkingCategoricalIntervalReversal
noncomputable section

/-- The original lifted codiscrete walking Hom types still have unique arrows. -/
instance walkingHomSubsingleton (x y : walkingIso.{u}) : Subsingleton (x ⟶ y) :=
  ⟨fun f g ↦ by
    rcases f with ⟨⟨⟩⟩
    rcases g with ⟨⟨⟩⟩
    rfl⟩

/-- Invert the original unique walking arrows, retaining their endpoints. -/
def oppositeToWalking : walkingIso.{u}ᵒᵖ ⥤ walkingIso.{u} where
  obj x := x.unop
  map _ := ⟨⟨⟩⟩
  map_id _ := rfl
  map_comp _ _ := rfl

/-- A simplicial map from the genuinely reversed interval to the original one. -/
def reversal : J.{u}.op ⟶ J.{u} :=
  nerveOppositeMap walkingIso ≫ nerveMap oppositeToWalking

/-- The same full parameter simplex, with its vertex order reversed. -/
def reverseParameter (n : SimplexCategoryᵒᵖ) (t : J.{u}.obj n) : J.{u}.obj n :=
  reversal.app n (SSet.opObjEquiv.symm t)

/-- The parameter reversal commutes with exactly the reversed simplex operators. -/
theorem reverseParameter_natural {n m : SimplexCategoryᵒᵖ} (i : n ⟶ m)
    (t : J.{u}.obj n) :
    reverseParameter m (J.map i t) =
      J.map (SimplexCategory.rev.map i.unop).op (reverseParameter n t) := by
  cases n with
  | op n =>
    cases m with
    | op m =>
      induction n using SimplexCategory.rec with
      | h a =>
        induction m using SimplexCategory.rec with
        | h b =>
          have h := congrFun (reversal.naturality (SimplexCategory.rev.map i.unop).op) t
          change reversal.app _ (J.op.map (SimplexCategory.rev.map i.unop).op t) =
            J.map (SimplexCategory.rev.map i.unop).op (reversal.app _ t) at h
          simpa [reverseParameter, SSet.op_map, SSet.opObjEquiv,
            SimplexCategory.rev_map_rev_map] using h

/-- Reversal fixes each original constant endpoint, in every simplicial dimension. -/
theorem reverseParameter_endpoint (b : Bool) {X : SSet.{u}}
    (n : SimplexCategoryᵒᵖ) (x : X.obj n) :
    reverseParameter n
        ((SSet.const (ComposableArrows.mk₀ (parameterObject b)) : X ⟶ J).app n x) =
      (SSet.const (ComposableArrows.mk₀ (parameterObject b)) : X ⟶ J).app n x := by
  apply CategoryTheory.Functor.ext (fun _ ↦ rfl)

/-- Both reversals retain every original interval simplex, not only its vertices. -/
theorem reverseParameter_involutive (n : SimplexCategoryᵒᵖ) (t : J.{u}.obj n) :
    reverseParameter n (reverseParameter n t) = t := by
  refine CategoryTheory.Functor.ext (fun j ↦ ?_) (fun _ _ _ ↦ Subsingleton.elim _ _)
  change t.obj j.rev.rev = t.obj j
  rw [Fin.rev_rev]

end
end DaggerActualWalkingCategoricalIntervalReversal
