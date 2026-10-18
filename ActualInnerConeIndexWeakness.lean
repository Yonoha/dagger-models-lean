import ActualInnerIteratedSecondConeProjection
import NativeDualTheoremASmallTarget
import NativeSimplexIndexNerveWeakContractibility
import NativeSmallHomNerveLiftForward

/-! The SAME original right-cone index is weak in the native inner family for ALL quasi X. -/
set_option autoImplicit false
open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra
open DaggerActualInnerIteratedRightConeIndex DaggerActualInnerIteratedConeFibreComparison
open DaggerActualInnerIteratedSecondConeProjection DaggerNativeSmallHomNerveLift
open DaggerNativeSimplexIndexNerveWeakContractibility DaggerSSetGluing
open DaggerOriginalProductGadget DaggerOriginalCounitRightConeQRealizationAdjunction
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerActualInnerConeIndexWeakness
noncomputable section

theorem second_comma_point_GW (X : SSet.{u}) (a b : X.obj (op ⦋0⦌))
    (Q : DaggerActualInnerIteratedGadgetShift.FibrantOver X a b) :
    GW (pointMap (nerve (CostructuredArrow (toPositive X a b) Q))) := by
  obtain ⟨Y, _hKan, hY, G, hG⟩ := all_positive_comparisons X a b Q
  have : WeakEquivalence (mixedMap G) := (weakEquivalence_iff_GW _).mpr hG
  have : WeakEquivalence (pointMap (nerve (DaggerNativeSimplexIndexResolution.Index Y))) :=
    (weakEquivalence_iff_GW _).mpr (index_point_GW Y hY)
  have he : mixedMap G ≫ pointMap (nerve (DaggerNativeSimplexIndexResolution.Index Y)) =
      pointMap (nerve (CostructuredArrow (toPositive X a b) Q)) := pointIsTerminal.hom_ext _ _
  apply (weakEquivalence_iff_GW _).mp
  rw [← he]
  infer_instance

theorem second_projection_GW (X : SSet.{u}) (a b : X.obj (op ⦋0⦌)) :
    GW (nerveMap (toPositive X a b)) :=
  DaggerNerveTheoremA.nerveMap_GW (toPositive X a b) (second_comma_point_GW X a b)

theorem first_projection_lifted_GW (X : SSet.{u}) [X.Quasicategory]
    (a b : X.obj (op ⦋0⦌)) :
    GW (nerveMap (toCones X a b ⋙ ULiftHom.up.{0, u, u})) :=
  DaggerNativeDualTheoremASmallTarget.lifted_nerveMap_GW (toCones X a b)
    (first_projection_under_point_GW X a b)

def raisedIndex (X : SSet.{u}) (a b : X.obj (op ⦋0⦌)) :=
  ULiftHom.down.{0, u, u} ⋙ index X a b

theorem raised_index_GW (X : SSet.{u}) [X.Quasicategory] (a b : X.obj (op ⦋0⦌)) :
    GW (nerveMap (raisedIndex X a b)) := by
  have : WeakEquivalence (nerveMap (toPositive X a b)) :=
    (weakEquivalence_iff_GW _).mpr (second_projection_GW X a b)
  have : WeakEquivalence (nerveMap (DaggerActualInnerIteratedGadgetShift.inclusion X a b)) :=
    (weakEquivalence_iff_GW _).mpr
      (DaggerActualInnerPositiveGadgetCofinality.inclusion_GW X a b)
  have hright : GW (nerveMap
      (toPositive X a b ⋙ DaggerActualInnerIteratedGadgetShift.inclusion X a b)) := by
    change GW (nerveMap (toPositive X a b) ≫
      nerveMap (DaggerActualInnerIteratedGadgetShift.inclusion X a b))
    exact (weakEquivalence_iff_GW _).mp inferInstance
  have hleft : GW (nerveMap (toCones X a b ⋙ index X a b)) :=
    (SSet.KanComplex.W.iff_homotopy
      (DaggerNerveHomotopy.natTransHomotopy (bridge X a b)).toTop.toSSet).mpr hright
  have : WeakEquivalence (nerveMap (toCones X a b ⋙ ULiftHom.up.{0, u, u})) :=
    (weakEquivalence_iff_GW _).mpr (first_projection_lifted_GW X a b)
  apply (weakEquivalence_iff_GW _).mp
  apply (weakEquivalence_precomp_iff
    (nerveMap (toCones X a b ⋙ ULiftHom.up.{0, u, u}))
    (nerveMap (raisedIndex X a b))).mp
  exact (weakEquivalence_iff_GW _).mpr hleft

end
end DaggerActualInnerConeIndexWeakness
