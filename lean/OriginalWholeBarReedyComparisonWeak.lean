import NativeBisimplicialDiagonalWeak
import OriginalWholeBarRelativeReedy

/-! BOTH exact original whole-bar/base comparison maps are native weak equivalences. -/
set_option autoImplicit false
open CategoryTheory HomotopicalAlgebra
open DaggerNativeBisimplicialDiagonalWeak DaggerOriginalWholeBarRelativeReedy
open DaggerOriginalWholeBarBisimplicial DaggerOriginalSimplicialCategoryBarRows
open DaggerNativeBisimplicialDiagonal DaggerNativeReedyRelativeReplacement
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerOriginalWholeBarReedyComparisonWeak
noncomputable section

theorem totalComparison_weak (C : DaggerModels.SimplicialCat.{u, u}) :
    WeakEquivalence (totalComparison C) := by
  have : WeakEquivalence (diagonalFunctor.map (totalUnit (barArrow C))) :=
    diagonal_map_weak _ (fun h ↦
      ((mem_trivialCofibrations_iff _).mp
        (DaggerNativeReedyRelativeReplacement.totalUnit_row_trivial (barArrow C) h)).2)
  unfold totalComparison
  infer_instance

theorem baseComparison_weak (C : DaggerModels.SimplicialCat.{u, u}) :
    WeakEquivalence (baseComparison C) := by
  have : WeakEquivalence (diagonalFunctor.map (baseUnit (barArrow C))) :=
    diagonal_map_weak _ (fun h ↦
      ((mem_trivialCofibrations_iff _).mp
        (DaggerNativeReedyRelativeReplacement.baseUnit_row_trivial (barArrow C) h)).2)
  unfold baseComparison
  infer_instance

end
end DaggerOriginalWholeBarReedyComparisonWeak
