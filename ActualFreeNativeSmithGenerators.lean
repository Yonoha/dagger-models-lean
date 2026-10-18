import ActualOriginalAntiJoyalSmithModelData

/-! The small image of the complete native Smith family under the original freeAnti functor. -/
set_option autoImplicit false
open CategoryTheory DaggerModels MorphismProperty
open DaggerModels.OriginalTaggedReverseFreeCompletion
open DaggerModels.OriginalAntiInvolutiveNormalMonoSaturation
open DaggerActualAntiJoyalMappingWeakProperties
universe u
namespace DaggerActualFreeNativeSmithGenerators
noncomputable section

abbrev nativeGenerators : MorphismProperty SSet.{u} :=
  DaggerNativeFullWeakSmithGenerators.generators.{u}

def generator (a : nativeGenerators.{u}.toSet) := freeAnti.map a.val.hom

def generators : MorphismProperty AntiInvolutiveSSet.{u} := ofHoms generator

instance generatorsSmall : IsSmall.{u} generators.{u} := isSmall_ofHoms _

theorem generators_le : generators.{u} ≤ normalMonos.{u} ⊓ weakEquivalences := by
  intro X Y f hf
  obtain ⟨a⟩ := hf
  have h := DaggerNativeFullWeakSmithGenerators.generators_le a.val.hom a.property
  have : Mono a.val.hom := h.1
  exact DaggerActualFreeAntiJoyalMappingWeak.freeAnti_map_normal_and_weak a.val.hom h.2

theorem right_iff_underlying {X Y : AntiInvolutiveSSet.{u}} (p : X ⟶ Y) :
    generators.rlp p ↔ DaggerNativeJoyalFirstFactorization.candidateFibrations p.hom := by
  constructor
  · intro hp
    rw [← DaggerNativeOriginalJoyalSmithModelData.generated_right_eq]
    intro A B i hi
    let a : nativeGenerators.toSet := ⟨Arrow.mk i, hi⟩
    have ha : generators (generator a) := ofHoms.mk a
    have hl : HasLiftingProperty (freeAnti.map i) p := hp (generator a) ha
    exact (freeAntiAdjunction.hasLiftingProperty_iff i p).mp hl
  · intro hp
    have hJ : nativeGenerators.rlp p.hom := by
      rwa [DaggerNativeOriginalJoyalSmithModelData.generated_right_eq]
    intro A B i hi
    obtain ⟨a⟩ := hi
    exact (freeAntiAdjunction.hasLiftingProperty_iff a.val.hom p).mpr
      (hJ a.val.hom a.property)

def factorization : generators.{u}.rlp.llp.FunctorialFactorizationData generators.{u}.rlp :=
  DaggerSmithSolutionSet.soaFactorization generators

end
end DaggerActualFreeNativeSmithGenerators
