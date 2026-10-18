import NativeHoIsoWholeWalkingHomotopy
import NativeKanTrivialCofibrationRestriction

/-! Native Kan trivial fibrations lift whole original J-paths with prescribed endpoints. -/
set_option autoImplicit false
open CategoryTheory Limits Simplicial HomotopicalAlgebra
open DaggerActualFreeWalkingIsoIntegerObstruction DaggerNativeHoIsoWalkingExtension
open DaggerNativeWalkingEdgeKanInclusion
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerNativeKanTrivialFibrationWalkingLifts
noncomputable section

theorem exists_walking_lift {E B : SSet.{u}} (p : E ⟶ B) [Fibration p] [WeakEquivalence p]
    (x0 x1 : E _⦋0⦌) (c : J.{u} ⟶ B)
    (h0 : SSet.yonedaEquiv.symm x0 ≫ p = zeroInclusion.{u} ≫ c)
    (h1 : SSet.yonedaEquiv.symm x1 ≫ p = oneInclusion.{u} ≫ c) :
    ∃ H : J.{u} ⟶ E, zeroInclusion.{u} ≫ H = SSet.yonedaEquiv.symm x0 ∧
      oneInclusion.{u} ≫ H = SSet.yonedaEquiv.symm x1 ∧ H ≫ p = c := by
  have : Cofibration (SSet.boundary.{u} 1).ι :=
    (SSet.modelCategoryQuillen.cofibration_iff _).mpr inferInstance
  let sq : CommSq (SSet.boundary₁.desc x0 x1) (SSet.boundary.{u} 1).ι p
      (edgeInclusion.{u} ≫ c) := ⟨by
    apply SSet.boundary₁.hom_ext
    · simp only [← Category.assoc, SSet.boundary₁.ι₀_desc, SSet.boundary₁.ι₀_ι,
        zero_edgeInclusion, h0]
    · simp only [← Category.assoc, SSet.boundary₁.ι₁_desc, SSet.boundary₁.ι₁_ι,
        one_edgeInclusion, h1]⟩
  have hc := edgeInclusion_trivial_cofibration.{u}
  have : Cofibration edgeInclusion.{u} := (mem_trivialCofibrations_iff _).mp hc |>.1
  have : WeakEquivalence edgeInclusion.{u} := (mem_trivialCofibrations_iff _).mp hc |>.2
  let sqJ : CommSq sq.lift edgeInclusion.{u} p c := ⟨sq.fac_right⟩
  refine ⟨sqJ.lift, ?_, ?_, sqJ.fac_right⟩
  · rw [← zero_edgeInclusion, Category.assoc, sqJ.fac_left]
    have hh := congrArg (fun f ↦ SSet.boundary₁.ι₀ ≫ f) sq.fac_left
    simpa only [← Category.assoc, SSet.boundary₁.ι₀_ι,
      SSet.boundary₁.ι₀_desc] using hh
  · rw [← one_edgeInclusion, Category.assoc, sqJ.fac_left]
    have hh := congrArg (fun f ↦ SSet.boundary₁.ι₁ ≫ f) sq.fac_left
    simpa only [← Category.assoc, SSet.boundary₁.ι₁_ι,
      SSet.boundary₁.ι₁_desc] using hh

end
end DaggerNativeKanTrivialFibrationWalkingLifts
