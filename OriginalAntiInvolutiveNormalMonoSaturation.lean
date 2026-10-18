import OriginalAntiInvolutiveNormalMonoCoproduct
import OriginalAntiInvolutiveNormalGenerators
import Mathlib.CategoryTheory.MorphismProperty.Limits

/-!
# The closure direction for the literal anti-involutive boundary generators

All degrees, including vertices, use the unchanged NormalMono predicate.
The actual freeAnti generators lie in it, and their coproduct/pushout/
transfinite/retract saturation still lies in it. The converse requires the
actual relative boundary attachment and is not assumed here.
-/

set_option autoImplicit false

open CategoryTheory Limits

universe u

namespace DaggerModels.OriginalAntiInvolutiveNormalMonoSaturation

open DaggerModels.AntiInvolutiveSSet
open DaggerModels.OriginalAntiInvolutiveNormalMonoClosure
open DaggerModels.OriginalAntiInvolutiveNormalMonoPushout
open DaggerModels.OriginalAntiInvolutiveNormalMonoTransfinite
open DaggerModels.OriginalAntiInvolutiveNormalMonoCoproduct
open DaggerModels.OriginalAntiInvolutiveNormalGenerators

/-- The unchanged all-degree predicate as a categorical morphism property. -/
abbrev normalMonos : MorphismProperty AntiInvolutiveSSet.{u} :=
  fun _ _ f ↦ NormalMono f

instance : normalMonos.{u}.ContainsIdentities where
  id_mem := normalMono_id

instance : normalMonos.{u}.IsStableUnderComposition where
  comp_mem _ _ := NormalMono.comp

instance : normalMonos.{u}.IsStableUnderRetracts where
  of_retract := NormalMono.of_retract

instance : normalMonos.{u}.IsStableUnderCobaseChange where
  of_isPushout sq hf := NormalMono.of_isPushout sq.flip hf

instance (I : Type u) : normalMonos.{u}.IsStableUnderCoproductsOfShape I :=
  MorphismProperty.IsStableUnderCoproductsOfShape.mk _ _
    (fun _ _ _ _ f hf ↦ NormalMono.sigma_map f hf)

instance : MorphismProperty.IsStableUnderCoproducts.{u} normalMonos.{u} where

instance (J : Type u) [LinearOrder J] [SuccOrder J] [OrderBot J] [WellFoundedLT J] :
    normalMonos.{u}.IsStableUnderTransfiniteCompositionOfShape J :=
  normalMono_isStableUnderTransfiniteCompositionOfShape J

instance : MorphismProperty.IsStableUnderTransfiniteComposition.{u} normalMonos.{u} where

/-- The actual freeAnti images of all ordinary simplex boundary inclusions. -/
def normalGeneratingCofibrations : MorphismProperty AntiInvolutiveSSet.{u} :=
  MorphismProperty.ofHoms (freeBoundary.{u})

/-- Each literal original boundary generator is normal, in every degree. -/
theorem normalGeneratingCofibrations_le_normalMonos :
    normalGeneratingCofibrations.{u} ≤ normalMonos.{u} := by
  intro X Y f hf
  obtain ⟨n⟩ := hf
  exact freeBoundary_normal n

/-- Saturating the original freeAnti generators cannot produce a non-normal
map. This is one direction of the full normal-generator recognition theorem. -/
theorem normalGeneratorSaturation_le_normalMonos :
    (MorphismProperty.transfiniteCompositions.{u}
      (MorphismProperty.coproducts.{u} normalGeneratingCofibrations.{u}).pushouts).retracts ≤
        normalMonos.{u} := by
  rw [MorphismProperty.retracts_le_iff, MorphismProperty.transfiniteCompositions_le_iff,
    MorphismProperty.pushouts_le_iff, MorphismProperty.coproducts_le_iff]
  exact normalGeneratingCofibrations_le_normalMonos

end DaggerModels.OriginalAntiInvolutiveNormalMonoSaturation
