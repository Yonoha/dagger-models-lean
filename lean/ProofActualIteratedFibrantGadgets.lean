import ChallengeActualIteratedFibrantGadgetsReconciled
import ActualIteratedFibrantInclusion
import ActualIteratedGadgetRightMapping
import ProofActualFibrantRightConeEndpoints

/-! Verify the short independent statement in the full saved model-category context. -/
set_option autoImplicit false
open CategoryTheory Opposite Simplicial DaggerModels OrdinaryRigidification
open DaggerActualIteratedGadgetData DaggerActualIteratedGadgetShift
open DaggerNerveHomotopy DaggerSSetGluing
universe u
namespace DaggerActualIteratedFibrantGadgetsProof
noncomputable section

/-- The exact full-map shift is weak on nerves by its literal unit transformation. -/
theorem over_GW (D : SimplicialCat.{u, u})
    (r : OriginalOrdinaryLocalKanReplacement.replacement.obj D ⟶ D)
    (hr : OriginalOrdinaryLocalKanReplacement.unit.app D ≫ r = 𝟙 D)
    (a b : (coherentNerve.obj D).obj (op ⦋0⦌)) : GW (nerveMap (over D r hr a b)) :=
  nerveMap_geometricW (over D r hr a b) (𝟭 _)
    (Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ ⟨overUnit D r hr a b⟩))
    (Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ ⟨overUnit D r hr a b⟩))

/-- All selected levels, whole maps, operators, and actual right-cone mapping objects are verified. -/
theorem verified : DaggerActualIteratedFibrantGadgetsChallenge.statement.{u} := by
  refine ⟨?_, ?_, ?_⟩
  · intro P
    exact ⟨DaggerActualIteratedGadgetProperties.endpoint_hom_GW P,
      DaggerActualIteratedGadgetProperties.positive_quasicategory P⟩
  · intro D hD a b
    obtain ⟨r, hr⟩ := DaggerActualFibrantGadgetExtensions.exists_retraction D hD
    refine ⟨r, hr, over D r hr a b, overUnit D r hr a b, ?_⟩
    exact ⟨fun _ ↦ rfl, fun _ ↦ HEq.rfl, fun _ ↦ HEq.rfl, fun _ _ _ ↦ HEq.rfl,
      over_GW D r hr a b, DaggerActualIteratedFibrantInclusion.inclusion_GW D r hr a b⟩
  · intro P k
    exact ⟨DaggerActualIteratedGadgetRightMapping.rightCone_Kan P k,
      DaggerActualIteratedGadgetRightMapping.rightCone_toUnit_GW P k⟩

end
end DaggerActualIteratedFibrantGadgetsProof
