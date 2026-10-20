import ChosenNecklaceLabelledPoint
import ChosenNecklaceEnrichedCut
import ChosenNecklaceCutPushout
import Mathlib.CategoryTheory.Adjunction.Limits

open CategoryTheory Limits EnrichedCategory MonoidalCategory Opposite Simplicial

universe u

namespace DaggerChosenRigidificationNecklace

noncomputable section

open NecklaceCode NecklaceThickening

variable (T : NecklaceCode) (j : Fin (T.len + 1)) (hj : j ∈ T.joints)
variable (L : LabelledComparison.{u} (cutLeft T j))
variable (R : LabelledComparison.{u} (cutRight T j))

def chosenCutIsPushout :
    IsPushout (C.map (pointAt (cutLeft T j) (ULift.up (Fin.last _))))
      (C.map (pointAt (cutRight T j) (ULift.up 0)))
      (C.map (cutLeftι.{u} T j)) (C.map (cutRightι T j)) := by
  let adj := DaggerModels.OrdinaryRigidification.rigidificationCoherentNerveAdjunction.{u}
  letI : PreservesColimitsOfSize.{0,0} C.{u} :=
    adj.leftAdjoint_preservesColimits
  exact (cutIsPushout T j hj).map C

/-- Same chosen-C pushout, with only the source objects identified by the specified isos. -/
def identifiedChosenCut :
    IsPushout (cutPointLeg.{u} T j false) (cutPointLeg T j true)
      (L.iso.inv ≫ C.map (cutLeftι T j)) (R.iso.inv ≫ C.map (cutRightι T j)) := by
  apply (chosenCutIsPushout T j hj).of_iso
    pointComparison.iso L.iso R.iso (Iso.refl _)
  · exact L.point_leg _
  · exact R.point_leg _
  · simp only [Iso.refl_hom, Category.comp_id, Iso.hom_inv_id_assoc]
  · simp only [Iso.refl_hom, Category.comp_id, Iso.hom_inv_id_assoc]

def cutChosenIso : C.{u}.obj T.toSSet ≅ NC.{u} T :=
  (identifiedChosenCut T j hj L R).isoIsPushout _ _ (cutNCIsPushout T j hj)

theorem cutChosenIso_left : C.map (cutLeftι.{u} T j) ≫ (cutChosenIso T j hj L R).hom =
    L.iso.hom ≫ cutNCInclusion T j false := by
  apply (cancel_epi L.iso.inv).mp
  simpa only [Category.assoc, Iso.inv_hom_id_assoc] using
    IsPushout.inl_isoIsPushout_hom _ _
      (identifiedChosenCut T j hj L R) (cutNCIsPushout T j hj)

theorem cutChosenIso_right : C.map (cutRightι.{u} T j) ≫ (cutChosenIso T j hj L R).hom =
    R.iso.hom ≫ cutNCInclusion T j true := by
  apply (cancel_epi R.iso.inv).mp
  simpa only [Category.assoc, Iso.inv_hom_id_assoc] using
    IsPushout.inr_isoIsPushout_hom _ _
      (identifiedChosenCut T j hj L R) (cutNCIsPushout T j hj)

end

end DaggerChosenRigidificationNecklace
