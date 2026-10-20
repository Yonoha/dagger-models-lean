import NativeOriginalFixedDaggerReplacement
import OriginalSimplicialPiZeroWeakEquivalence

/-! Keep the ORIGINAL R unit and ORIGINAL coherent-unitary witness; no Kan premise is added. -/
set_option autoImplicit false
open CategoryTheory HomotopicalAlgebra DaggerModels DaggerUnitaryInvariance
open DaggerOriginalFixedObjectDaggerCategories DaggerOriginalFixedObjectLegacyDaggerEquivalence
open DaggerNativeOriginalFixedDaggerReplacement DaggerOriginalSimplicialPiZeroWeakEquivalence
open scoped SSet.modelCategoryQuillen DaggerOriginalFixedObjectAmbientDaggerModel
universe u
namespace DaggerNativeOriginalCoherentUnitaryExistence
noncomputable section

variable (R : FunctorialFibrantReplacement.{u}) (C : DaggerSimplicialCat.{u, u}) (x y : C.Obj)

theorem original_unit_piZero_bijective :
    Function.Bijective ((piZeroEval DaggerUnitaryInterval.Vertex
      DaggerUnitaryInterval.left DaggerUnitaryInterval.right).map
        (R.unit.app (twoObjectCopy C x y))) := by
  let A := fromLegacyObject (twoObjectCopy C x y)
  have hw : WeakEquivalence (unit R A) := unit_weak R A
  have hm : WeakEquivalence ((unit R A).underlying.map
      DaggerUnitaryInterval.left DaggerUnitaryInterval.right) :=
    (DaggerOriginalFixedObjectAmbientDaggerModel.weakEquivalence_iff_original _).1 hw _ _
  have hb := bijective_mapPiZero ((unit R A).underlying.map
    DaggerUnitaryInterval.left DaggerUnitaryInterval.right)
  change Function.Bijective ((piZeroEval DaggerUnitaryInterval.Vertex
    DaggerUnitaryInterval.left DaggerUnitaryInterval.right).map (toLegacyHom (unit R A))) at hb
  simpa only [unit, roundtrip_hom] using hb

theorem some_coherent_component_iff_interval_map :
    (∃ z, CoherentlyUnitary R C x y z) ↔
      ∃ H : DaggerUnitaryInterval.Interval.{u},
        Nonempty (H.C ⟶ R.functor.obj (twoObjectCopy C x y)) := by
  change (∃ z H f, intervalEval H f =
    (piZeroEval DaggerUnitaryInterval.Vertex DaggerUnitaryInterval.left
      DaggerUnitaryInterval.right).map (R.unit.app (twoObjectCopy C x y)) z) ↔ _
  constructor
  · rintro ⟨z, H, f, _hf⟩
    exact ⟨H, ⟨f⟩⟩
  · rintro ⟨H, ⟨f⟩⟩
    obtain ⟨z, hz⟩ := (original_unit_piZero_bijective R C x y).surjective (intervalEval H f)
    exact ⟨z, H, f, hz.symm⟩

end
end DaggerNativeOriginalCoherentUnitaryExistence
