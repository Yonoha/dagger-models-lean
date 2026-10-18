import ActualInnerIteratedGadgetNecklaceComparison
import ActualInnerIteratedGadgetShift
import NativePositiveStructuredArrowContraction

/-! Positive native inner iterates are cofinal over EVERY original quasi-category X. -/
set_option autoImplicit false
open CategoryTheory Limits Opposite Simplicial
open DaggerActualInnerIteratedGadgetData DaggerActualInnerIteratedGadgetShift
open DaggerNerveHomotopy DaggerSSetGluing DaggerOriginalProductGadget
universe u
namespace DaggerActualInnerPositiveGadgetCofinality
noncomputable section

variable (X : SSet.{u}) [X.Quasicategory] (a b : X.obj (op ⦋0⦌))

theorem inclusion_GW : GW (nerveMap (inclusion X a b)) := by
  obtain ⟨r, hr⟩ := DaggerActualInnerReplacementExtensions.exists_retraction X
  exact nerveMap_geometricW (inclusion X a b) (toFibrant X r hr a b)
    (Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ ⟨fibrantUnit X r hr a b⟩))
    (Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ ⟨allUnit X r hr a b⟩))

theorem structured_point_GW (O : Over X a b) :
    GW (pointMap (nerve (StructuredArrow O (inclusion X a b)))) := by
  obtain ⟨r, hr⟩ := DaggerActualInnerReplacementExtensions.exists_retraction X
  exact DaggerNativePositiveStructuredArrowContraction.selected_point_GW
    (positive X a b) (over X r hr a b) (overUnit X r hr a b) (fun _ ↦ Nat.succ_pos _) O

end
end DaggerActualInnerPositiveGadgetCofinality
