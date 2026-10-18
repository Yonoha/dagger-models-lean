import NativeSimplexIndexNerveWeakContractibility

/-! The actual second projection has contractible literal comma nerves and is weak. -/
set_option autoImplicit false
open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra
open DaggerModels OrdinaryRigidification DaggerSSetGluing DaggerOriginalProductGadget
open DaggerActualIteratedRightConeIndex DaggerNativeSmallHomNerveLift
open DaggerNativeSimplexIndexNerveWeakContractibility
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerActualIteratedSecondConeProjectionWeakness
noncomputable section

/-- Every original positive object gives a weakly contractible actual second-projection comma. -/
theorem comma_point_GW (D : SimplicialCat.{u, u})
    (a b : (coherentNerve.obj D).obj (op ⦋0⦌))
    (Q : DaggerActualIteratedGadgetShift.FibrantOver D a b) :
    GW (pointMap (nerve (CostructuredArrow (toPositive D a b) Q))) := by
  obtain ⟨X, _hKan, hX, G, hG⟩ :=
    DaggerActualIteratedSecondConeProjection.all_positive_comparisons D a b Q
  have : WeakEquivalence (mixedMap G) := (weakEquivalence_iff_GW _).mpr hG
  have : WeakEquivalence (pointMap (nerve (DaggerNativeSimplexIndexResolution.Index X))) :=
    (weakEquivalence_iff_GW _).mpr (index_point_GW X hX)
  have he : mixedMap G ≫ pointMap (nerve (DaggerNativeSimplexIndexResolution.Index X)) =
      pointMap (nerve (CostructuredArrow (toPositive D a b) Q)) :=
    pointIsTerminal.hom_ext _ _
  apply (weakEquivalence_iff_GW _).mp
  rw [← he]
  infer_instance

/-- Native Theorem A applies to the original second projection with the original comma fibres. -/
theorem second_projection_GW (D : SimplicialCat.{u, u})
    (a b : (coherentNerve.obj D).obj (op ⦋0⦌)) :
    GW (nerveMap (toPositive D a b)) :=
  DaggerNerveTheoremA.nerveMap_GW (toPositive D a b) (comma_point_GW D a b)

end
end DaggerActualIteratedSecondConeProjectionWeakness
