import ActualQWeightedResolutionNaturality
import NativeSimplicialReplacementReindexMonos

/-! The unchanged Q-weighted replacement map preserves actual Kan-Quillen cofibrations. -/
set_option autoImplicit false
open CategoryTheory HomotopicalAlgebra
open DaggerActualQWeightedResolutionNaturality
open DaggerNativeSimplexIndexResolutionNaturality
open DaggerNativeFullChainInjectivity DaggerNativeSimplicialReplacementReindexMonos
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerActualQWeightedResolutionCofibrations
noncomputable section

variable {X Y : SSet.{u}} (f : X ⟶ Y)

/-- Mono postcomposition recovers each entire original simplex-index object. -/
theorem index_obj_injective [Mono f] : Function.Injective (indexMap f).obj :=
  costructured_map_obj_injective uliftYoneda f

/-- No Q parameter or simplex-index arrow is discarded by the original resolution map. -/
theorem map_mono [Mono f] : Mono (DaggerActualQWeightedResolutionNaturality.map f) := by
  have : (indexMap f).Faithful := by
    constructor
    intro P Q g h he
    apply ULift.ext
    exact CostructuredArrow.ext g.down h.down (congrArg (fun m ↦ m.down.left) he)
  exact diagonalReindex_mono (indexMap f) (index_obj_injective f) (weights Y)

/-- Preserve cofibrations of the actual Kan-Quillen model, on the unchanged map. -/
theorem map_cofibration [Cofibration f] :
    Cofibration (DaggerActualQWeightedResolutionNaturality.map f) := by
  have : Mono f := inferInstance
  have : Mono (DaggerActualQWeightedResolutionNaturality.map f) := map_mono f
  exact SSet.modelCategoryQuillen.cofibration_of_mono _

end
end DaggerActualQWeightedResolutionCofibrations
