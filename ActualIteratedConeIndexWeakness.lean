import ActualIteratedFirstConeProjectionWeakness
import ActualIteratedSecondConeProjectionWeakness
import ActualIteratedFibrantInclusion
import NativeSmallHomNerveLiftForward

/-! The unchanged right-cone simplex index is weak in the actual iterated gadget category. -/
set_option autoImplicit false
open CategoryTheory Opposite Simplicial HomotopicalAlgebra DaggerModels OrdinaryRigidification
open DaggerActualIteratedRightConeIndex DaggerOriginalProductGadget DaggerSSetGluing
open DaggerOriginalCounitBNextConeEvaluationIndex
open DaggerOriginalCounitRightConeQRealizationAdjunction
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerActualIteratedConeIndexWeakness
noncomputable section

/-- The cone index with only its source hom universe raised. -/
def raisedIndex (D : SimplicialCat.{u, u})
    (a b : (coherentNerve.obj D).obj (op ⦋0⦌)) :=
  ULiftHom.down.{0, u, u} ⋙ index D a b

/-- Both projections and the actual full comma transformation force the raised cone index weak. -/
theorem raised_index_GW (D : SimplicialCat.{u, u})
    (hD : ∀ x y : D.Obj, SSet.KanComplex (x ⟶[SSet.{u}] y))
    (a b : (coherentNerve.obj D).obj (op ⦋0⦌)) :
    GW (nerveMap (raisedIndex D a b)) := by
  obtain ⟨r, hr⟩ := DaggerActualFibrantGadgetExtensions.exists_retraction D hD
  have : WeakEquivalence (nerveMap (toPositive D a b)) :=
    (weakEquivalence_iff_GW _).mpr
      (DaggerActualIteratedSecondConeProjectionWeakness.second_projection_GW D a b)
  have : WeakEquivalence (nerveMap (DaggerActualIteratedGadgetShift.inclusion D a b)) :=
    (weakEquivalence_iff_GW _).mpr
      (DaggerActualIteratedFibrantInclusion.inclusion_GW D r hr a b)
  have hright : GW (nerveMap
      (toPositive D a b ⋙ DaggerActualIteratedGadgetShift.inclusion D a b)) := by
    change GW (nerveMap (toPositive D a b) ≫
      nerveMap (DaggerActualIteratedGadgetShift.inclusion D a b))
    exact (weakEquivalence_iff_GW _).mp inferInstance
  have hleft : GW (nerveMap (toCones D a b ⋙ index D a b)) :=
    (SSet.KanComplex.W.iff_homotopy
      (DaggerNerveHomotopy.natTransHomotopy (bridge D a b)).toTop.toSSet).mpr hright
  have : WeakEquivalence (nerveMap (toCones D a b ⋙ ULiftHom.up.{0, u, u})) :=
    (weakEquivalence_iff_GW _).mpr
      (DaggerActualIteratedFirstConeProjectionWeakness.first_projection_lifted_GW D hD a b)
  apply (weakEquivalence_iff_GW _).mp
  apply (weakEquivalence_precomp_iff
    (nerveMap (toCones D a b ⋙ ULiftHom.up.{0, u, u}))
    (nerveMap (raisedIndex D a b))).mp
  exact (weakEquivalence_iff_GW _).mpr hleft

/-- The whole original cone index is weak, with every original cone simplex operator retained. -/
theorem index_GW (D : SimplicialCat.{u, u})
    (hD : ∀ x y : D.Obj, SSet.KanComplex (x ⟶[SSet.{u}] y))
    (a b : (coherentNerve.obj D).obj (op ⦋0⦌)) :
    GW (DaggerNativeSmallHomNerveLiftForward.mixedMap (index D a b)) := by
  have : WeakEquivalence (DaggerNativeSmallHomNerveLift.upMap
      (CostructuredArrow uliftYoneda.{u, 0, 0}
        (rightConeSimplices D a b))) := by
    change WeakEquivalence (DaggerNativeSmallHomNerveLift.iso _).hom
    infer_instance
  have : WeakEquivalence (nerveMap (raisedIndex D a b)) :=
    (weakEquivalence_iff_GW _).mpr (raised_index_GW D hD a b)
  apply (weakEquivalence_iff_GW _).mp
  rw [← DaggerNativeSmallHomNerveLiftForward.up_mixedMap]
  exact (show WeakEquivalence
    (DaggerNativeSmallHomNerveLift.upMap
      (CostructuredArrow uliftYoneda.{u, 0, 0} (rightConeSimplices D a b)) ≫
        nerveMap (raisedIndex D a b)) from inferInstance)

end
end DaggerActualIteratedConeIndexWeakness
