import NativeGeometricPiWeakPullback
import OriginalBarRowsLocalWeakPreservation
import OriginalGeometricBasedPiProjection
import OriginalLocalKanReplacementDiagonalWeak

/-! Both original, unreplaced row diagrams satisfy geometric pi Kan without original Hom Kan. -/
set_option autoImplicit false
open CategoryTheory Simplicial Opposite HomotopicalAlgebra DaggerModels
open DaggerNativeGeometricPiVertexPullback DaggerNativeGeometricPiWeakPullback
open DaggerOriginalGeometricBasedPiProjection DaggerOriginalSimplicialCategoryBarRows
open DaggerOriginalNerveRowChainData DaggerOriginalNerveLocalWeakPreservation
open DaggerOriginalCotensorEvaluationRowMaps DaggerOriginalBarRowsLocalWeakPreservation
open DaggerOriginalAmbientDaggerPiZeroGroupoid DaggerOriginalLocalKanReplacementDiagonalWeak
open OriginalOrdinaryLocalKanReplacement
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerOriginalUnreplacedGeometricPiKan
noncomputable section

theorem original_base_geometric_pi_fibration (n : ℕ) (C : SimplicialCat.{u, u})
    (hC : HasActualComponentGroupoid C) :
    Fibration (geometricProjection (baseRows C) (n + 1)) := by
  have := replacement_base_geometric_based_pi_fibration n C hC
  apply geometricProjection_fibration_of_rowwise_weak (baseRowsMap (unit.app C))
  intro k
  obtain ⟨k⟩ := k
  induction k using SimplexCategory.rec with | _ k =>
    exact baseRowsMap_weak (unit.app C) (unit_obj_bijective C) (unit_hom_weak C) k

theorem original_bar_geometric_pi_fibration (n : ℕ) (C : SimplicialCat.{u, u})
    (hC : HasActualComponentGroupoid C) (z : C.Obj) :
    Fibration (geometricProjection (barRows C z) (n + 1)) := by
  have := replacement_bar_geometric_based_pi_fibration n C hC ((unit.app C).obj z)
  apply geometricProjection_fibration_of_rowwise_weak (barRowsMap (unit.app C) z)
  intro k
  obtain ⟨k⟩ := k
  induction k using SimplexCategory.rec with | _ k =>
    exact barRowsMap_weak (unit.app C) (unit_obj_bijective C) (unit_hom_weak C) z k

end
end DaggerOriginalUnreplacedGeometricPiKan
