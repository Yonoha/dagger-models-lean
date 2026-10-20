import OriginalWholeBarRelativeNativePiKan
import OriginalWholeBarComponentFibration
import OriginalReedyNativePiKan
import NativePiKanReedyDiagonal

/-! The ACTUAL whole-bar relative replacement has its original diagonal projection fibration. -/
set_option autoImplicit false
open CategoryTheory HomotopicalAlgebra DaggerModels
open DaggerOriginalWholeBarRelativeReedy DaggerOriginalWholeBarRelativeNativePiKan
open DaggerOriginalWholeBarComponentFibration DaggerOriginalReedyNativePiKan
open DaggerOriginalAmbientDaggerPiZeroGroupoid
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerOriginalWholeBarReedyDiagonalFibration
noncomputable section

theorem projection_fibration (C : SimplicialCat.{u, u})
    (hC : HasActualComponentGroupoid C) : Fibration (projection C) := by
  have : Fibration (C := SSet.{u})
      (DaggerNativeComponentMatchingNaturality.componentMap (replacedBar C).hom) :=
    replaced_whole_component_projection_fibration C hC
  exact DaggerNativePiKanReedyDiagonal.diagonal_fibration (replacedBar C).hom
    (bar_projection_reedy C) (bar_total_reedy C) (bar_base_reedy C)
    (fun n ↦ replaced_whole_native_pi_fibration n C hC)
    (fun n ↦ whole_bar_replaced_base_native_pi_fibration n C hC)

end
end DaggerOriginalWholeBarReedyDiagonalFibration
