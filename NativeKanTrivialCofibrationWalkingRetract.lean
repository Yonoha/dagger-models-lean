import NativeKanTrivialFibrationWalkingLifts
import NativeConstantIhomMaps

/-! Native Kan trivial cofibrations between Kan objects have whole relative J deformations. -/
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory Simplicial HomotopicalAlgebra
open DaggerActualFreeWalkingIsoIntegerObstruction DaggerActualFreeAntiWalkingCategoricalCylinder
open DaggerNativeHoIsoWalkingExtension DaggerNativeHoIsoWholeWalkingHomotopy
open DaggerNativeConstantIhomMaps DaggerNativeIhomHoObjects
open DaggerNativeKanTrivialCofibrationRestriction DaggerNativeKanTrivialFibrationWalkingLifts
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerNativeKanTrivialCofibrationWalkingRetract
noncomputable section

theorem exists_relative_walking_retract {A B : SSet.{u}} [A.KanComplex] [B.KanComplex]
    (j : A ⟶ B) [Cofibration j] [WeakEquivalence j] :
    ∃ (r : B ⟶ A) (H : B ⊗ J.{u} ⟶ B), j ≫ r = 𝟙 A ∧
      intervalEndpoint B false ≫ H = r ≫ j ∧ intervalEndpoint B true ≫ H = 𝟙 B ∧
      (j ▷ J.{u}) ≫ H = fst A J.{u} ≫ j := by
  let sq : CommSq (𝟙 A) j (terminal.from A) (terminal.from B) := ⟨by simp⟩
  let r := sq.lift
  have hjr : j ≫ r = 𝟙 A := sq.fac_left
  let p := (MonoidalClosed.pre j).app B
  have ht := restriction_trivial_fibration j B
  have : Fibration p := (mem_trivialFibrations_iff _).mp ht |>.1
  have : WeakEquivalence p := (mem_trivialFibrations_iff _).mp ht |>.2
  let x0 := SSet.hoFunctor.obj.equiv ((ihom B).obj B) (homObject (r ≫ j))
  let x1 := SSet.hoFunctor.obj.equiv ((ihom B).obj B) (homObject (𝟙 B))
  have h0 : SSet.yonedaEquiv.symm x0 ≫ p = zeroInclusion.{u} ≫ constantHom J.{u} j := by
    rw [← constantHom_point, constantHom_pre, constantHom_comp]
    congr 1
    rw [← Category.assoc, hjr, Category.id_comp]
  have h1 : SSet.yonedaEquiv.symm x1 ≫ p = oneInclusion.{u} ≫ constantHom J.{u} j := by
    rw [← constantHom_point, constantHom_pre, constantHom_comp, Category.comp_id]
  obtain ⟨H, hH0, hH1, hHp⟩ := exists_walking_lift p x0 x1 (constantHom J.{u} j) h0 h1
  refine ⟨r, MonoidalClosed.uncurry H, hjr, ?_, ?_, ?_⟩
  · exact uncurry_endpoint (r ≫ j) H false
      (point_comp_eq_curry (r ≫ j) H false zeroInclusion rfl hH0)
  · exact uncurry_endpoint (𝟙 B) H true
      (point_comp_eq_curry (𝟙 B) H true oneInclusion rfl hH1)
  · have h := congrArg MonoidalClosed.uncurry hHp
    simpa only [p, MonoidalClosed.uncurry_pre_app, uncurry_constant] using h

end
end DaggerNativeKanTrivialCofibrationWalkingRetract
