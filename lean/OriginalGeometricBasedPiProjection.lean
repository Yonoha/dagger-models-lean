import NativeGeometricPiProjectionFibration
import OriginalRealizedBasedPiProjection

/-! Geometric pi horn lifting over the original vertices of both exact R(C) row diagrams. -/
set_option autoImplicit false
open CategoryTheory Simplicial HomotopicalAlgebra DaggerModels
open DaggerNativeGeometricPiVertexPullback DaggerNativeGeometricPiProjectionFibration
open DaggerOriginalRealizedBasedPiProjection DaggerOriginalSimplicialCategoryBarRows
open DaggerOriginalAmbientDaggerPiZeroGroupoid OriginalOrdinaryLocalKanReplacement
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerOriginalGeometricBasedPiProjection
noncomputable section

theorem replacement_base_geometric_based_pi_fibration (n : ℕ) (C : SimplicialCat.{u, u})
    (hC : HasActualComponentGroupoid C) :
    Fibration (geometricProjection (baseRows (replacement.obj C)) (n + 1)) := by
  have := replacement_realized_base_based_pi_fibration n C hC
  exact geometricProjection_fibration _ (n + 1)

theorem replacement_bar_geometric_based_pi_fibration (n : ℕ) (C : SimplicialCat.{u, u})
    (hC : HasActualComponentGroupoid C) (z : (replacement.obj C).Obj) :
    Fibration (geometricProjection (barRows (replacement.obj C) z) (n + 1)) := by
  have := replacement_realized_bar_based_pi_fibration n C hC z
  exact geometricProjection_fibration _ (n + 1)

end
end DaggerOriginalGeometricBasedPiProjection
