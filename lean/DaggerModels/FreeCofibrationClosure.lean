import DaggerModels.FreeCofibrationCoproduct
import DaggerModels.FreeCofibrationPushout
import DaggerModels.FreeCofibrationTransfinite
import Mathlib.CategoryTheory.MorphismProperty.Limits

/-!
# Categorical closure operations for free cofibrations

We package the proved closure properties of the unchanged predicate from
Part I, `dj.def.free-cof`, using mathlib's categorical closure operations.
This supplies the closure direction in `dj.lem.free-cof`; the converse
requires the actual relative boundary-cell presentation.
-/

open CategoryTheory Limits

universe u

namespace DaggerModels.DaggerSSet

/-- The original free-cofibration predicate as a categorical morphism property. -/
abbrev freeCofibrations : MorphismProperty DaggerSSet.{u} :=
  fun _ _ f ↦ FreeCofibration f

instance : freeCofibrations.{u}.ContainsIdentities where
  id_mem := freeCofibration_id

instance : freeCofibrations.{u}.IsStableUnderComposition where
  comp_mem _ _ := FreeCofibration.comp

instance : freeCofibrations.{u}.IsStableUnderRetracts where
  of_retract := FreeCofibration.of_retract

instance : freeCofibrations.{u}.IsStableUnderCobaseChange where
  of_isPushout sq hf := FreeCofibration.of_isPushout sq.flip hf

instance (I : Type u) : freeCofibrations.{u}.IsStableUnderCoproductsOfShape I :=
  MorphismProperty.IsStableUnderCoproductsOfShape.mk _ _
    (fun _ _ _ _ f hf ↦ FreeCofibration.sigma_map f hf)

instance : MorphismProperty.IsStableUnderCoproducts.{u} freeCofibrations.{u} where

instance (J : Type u) [LinearOrder J] [SuccOrder J] [OrderBot J] [WellFoundedLT J] :
    freeCofibrations.{u}.IsStableUnderTransfiniteCompositionOfShape J :=
  freeCofibration_isStableUnderTransfiniteCompositionOfShape J

instance : MorphismProperty.IsStableUnderTransfiniteComposition.{u} freeCofibrations.{u} where

/-- The original class is closed under the saturation operations used in `dj.lem.free-cof`.
This equality does not yet identify it with the saturation of the boundary generators. -/
theorem freeCofibrations_saturated :
    (MorphismProperty.transfiniteCompositions.{u}
      (MorphismProperty.coproducts.{u} freeCofibrations.{u}).pushouts).retracts =
        freeCofibrations.{u} := by
  apply le_antisymm
  · rw [MorphismProperty.retracts_le_iff, MorphismProperty.transfiniteCompositions_le_iff,
      MorphismProperty.pushouts_le_iff, MorphismProperty.coproducts_le_iff]
  · exact freeCofibrations.le_coproducts.trans
      ((MorphismProperty.coproducts.{u} freeCofibrations).le_pushouts.trans
        ((MorphismProperty.le_transfiniteCompositions _).trans
          (MorphismProperty.le_retracts _)))

end DaggerModels.DaggerSSet
