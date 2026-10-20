import OriginalPiZeroBarRowsKan
import NativeOverGroupoidNerveFibration

/-! The original vertical-pi0 bar-to-base row map is a genuine native Kan-model fibration. -/
set_option autoImplicit false
open CategoryTheory HomotopicalAlgebra DaggerModels
open DaggerOriginalBarRowsPiZero DaggerOriginalNerveRowsPiZero
open DaggerOriginalSimplicialPiZeroCategory DaggerOriginalAmbientDaggerPiZeroGroupoid
open DaggerNativeOverGroupoidNerveFibration
open OriginalOrdinaryLocalKanReplacement DaggerOriginalPiZeroGroupoidLocalWeakInvariance
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerOriginalPiZeroBarProjectionFibration
noncomputable section

theorem component_projection_fibration (C : SimplicialCat.{u, u})
    (hC : HasActualComponentGroupoid C) (z : C.Obj) :
    Fibration (componentRowProjection C z) := by
  obtain ⟨G, hG⟩ := hC
  have hP : Fibration (nerveMap (Over.forget (T := componentObjects C) z)) := by
    change Fibration (nerveMap (@Over.forget (componentObjects C) (componentCategory C) z))
    rw [← hG]
    letI : Groupoid.{u} (componentObjects C) := G
    exact over_forget_nerve_fibration (componentObjects C) z
  let a : Arrow.mk (componentRowProjection C z) ≅
      Arrow.mk (nerveMap (Over.forget (T := componentObjects C) z)) :=
    Arrow.isoMk (barComponentRowsIso C z) (componentRowsIso C) (by
      simpa using (componentRowsIso_projection C z).symm)
  exact (HomotopicalAlgebra.fibration_iff _).mpr
    (((fibrations SSet.{u}).arrow_mk_iso_iff a).mpr
      ((HomotopicalAlgebra.fibration_iff _).mp hP))

theorem replacement_component_projection_fibration (C : SimplicialCat.{u, u})
    (hC : HasActualComponentGroupoid C) (z : (replacement.obj C).Obj) :
    Fibration (componentRowProjection (replacement.obj C) z) :=
  component_projection_fibration (replacement.obj C) ((replacement_groupoid_iff C).mp hC) z

end
end DaggerOriginalPiZeroBarProjectionFibration
