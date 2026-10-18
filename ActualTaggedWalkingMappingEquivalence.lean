import NativeWalkingRetractionMappingEquivalence

/-!
# The literal whole original tagged generator passes every mapping-category test

Specialize the native closed-category construction to the previously verified
actual anti-involutive retraction, retaining both freeAnti copies and every simplex.
-/
set_option autoImplicit false
open CategoryTheory MonoidalCategory CartesianMonoidalCategory Simplicial DaggerModels
open DaggerModels.OriginalTaggedReverseFreeCompletion
open DaggerActualFreeWalkingIsoIntegerObstruction
open DaggerActualTaggedWalkingIsoImageDKObstruction
open DaggerActualTaggedWalkingCategoricalRetraction
open DaggerNativeWalkingRetractionMappingEquivalence
universe u
namespace DaggerActualTaggedWalkingMappingEquivalence
noncomputable section

theorem underlying_retraction : taggedGenerator.{u}.hom ≫ taggedCollapse.{u}.hom = 𝟙 _ :=
  congrArg (fun k ↦ k.hom) taggedGenerator_retraction

/-- Its forward functor is the native internal Hom precomposition with the original map. -/
def taggedMappingEquivalence (Z : SSet.{u}) :
    SSet.hoFunctor.obj ((ihom (freeAnti.obj J.{u}).toSSet).obj Z) ≌
    SSet.hoFunctor.obj ((ihom (freeAnti.obj (Δ[0] : SSet.{u})).toSSet).obj Z) :=
  mappingEquivalence taggedGenerator.hom taggedCollapse.hom underlying_retraction
    taggedCylinder taggedCylinder_zero taggedCylinder_one Z

/-- This is the actual precomposition functor, for every simplicial target. -/
theorem tagged_pre_isEquivalence (Z : SSet.{u}) :
    (SSet.hoFunctor.map ((MonoidalClosed.pre taggedGenerator.{u}.hom).app Z)).toFunctor.IsEquivalence :=
  show (taggedMappingEquivalence Z).functor.IsEquivalence by infer_instance

end
end DaggerActualTaggedWalkingMappingEquivalence
