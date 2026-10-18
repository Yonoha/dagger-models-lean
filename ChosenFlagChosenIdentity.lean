import ChosenFlagChosenHomCocone
import ChosenFlagEnrichment

open CategoryTheory EnrichedCategory MonoidalCategory Opposite Simplicial

universe u

namespace DaggerChosenRigidificationNecklace

noncomputable section

open NecklaceCode NecklaceThickening

theorem pointFlag_identity (q : SimplexCategoryᵒᵖ) :
    (outerFlagIso.{u} point).hom.app q (NecklaceCode.Flag.pointFlag q.unop.len) =
      (eId SSet (outerLeft point)).app q PUnit.unit := by
  refine CategoryTheory.Functor.ext (fun _ ↦ JointPath.ext ?_)
  change (Set.univ : Set (Vertices.{u} point)) = {ULift.up 0}
  apply Set.ext
  intro v
  simp only [Set.mem_univ, Set.mem_singleton_iff, true_iff]
  apply ULift.ext
  apply Fin.ext
  have h := v.down.isLt
  change v.down.val < 1 at h
  change v.down.val = 0
  omega

/-- The original point representative maps to the actual enriched identity, in every degree. -/
theorem chosenFlagHom_identity (X : SSet.{u}) (a : X.obj (op ⦋0⦌)) :
    flagIdentity X a ≫ chosenFlagHom X a a = eId SSet (RV X a) := by
  apply NatTrans.ext
  funext q v
  cases v
  change (targetHomTransport
      (overChosenFunctor_first (NecklacesOver.point a))
      (overChosenFunctor_last (NecklacesOver.point a))).app q
    (((overChosenFunctor (NecklacesOver.point a)).map
      (outerLeft point) (outerRight point)).app q
      ((outerFlagIso point).hom.app q (NecklaceCode.Flag.pointFlag q.unop.len))) = _
  rw [pointFlag_identity]
  exact congrFun (NatTrans.congr_app
    (targetHomTransport_id (overChosenFunctor (NecklacesOver.point a))
      (outerLeft point) (RV X a) (overChosenFunctor_first (NecklacesOver.point a))) q)
    PUnit.unit

end

end DaggerChosenRigidificationNecklace
