import NativeReedyGeneratingLifting
import NativeBoxUnionRowsAnodyne
import Mathlib.CategoryTheory.Adjunction.Evaluation
import Mathlib.CategoryTheory.LiftingProperties.Adjunction

/-! Native row evaluation adjunctions make every generated left map rowwise anodyne. -/
set_option autoImplicit false
open CategoryTheory MorphismProperty HomotopicalAlgebra Simplicial Opposite
open DaggerNativeBisimplicialHorizontalMapping DaggerNativeReedySmallObject
open DaggerNativeReedyGeneratingLifting DaggerNativeBoxUnionRowsAnodyne
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerNativeReedySmallObjectRows
noncomputable section

theorem generator_row_trivial (m n : ℕ) (k : Fin (n + 2)) (h : SimplexCategoryᵒᵖ) :
    trivialCofibrations SSet.{u} ((generator.{u} m n k).app h) := by
  have : WeakEquivalence (SSet.horn.{u} (n + 1) k).ι :=
    ((mem_trivialCofibrations_iff _).mp (horn_trivial n k)).2
  exact row_trivial (SSet.boundary m) (SSet.horn (n + 1) k) h

theorem left_rows_trivial {F G : BiSSet.{u}} (i : F ⟶ G) (hi : J.rlp.llp i)
    (h : SimplexCategoryᵒᵖ) : trivialCofibrations SSet.{u} (i.app h) := by
  rw [← fibrations_llp]
  intro A B p hp
  have : Fibration (C := SSet.{u}) p := (fibration_iff _).mpr hp
  have hr : J.rlp ((evaluationRightAdjoint SSet.{u} h).map p) := by
    rintro U V j ⟨⟨m, n, k⟩⟩
    apply ((evaluationAdjunctionLeft SSet.{u} h).hasLiftingProperty_iff _ p).mp
    have ht := generator_row_trivial m n k h
    have : Cofibration ((generator.{u} m n k).app h) :=
      ((mem_trivialCofibrations_iff _).mp ht).1
    have : WeakEquivalence ((generator.{u} m n k).app h) :=
      ((mem_trivialCofibrations_iff _).mp ht).2
    change HasLiftingProperty ((generator.{u} m n k).app h) p
    infer_instance
  exact ((evaluationAdjunctionLeft SSet.{u} h).hasLiftingProperty_iff i p).mpr (hi _ hr)

end
end DaggerNativeReedySmallObjectRows
