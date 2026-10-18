import NativeOriginalRightOppositeLeftTransport
import NativeOriginalSigmaRightConeHomIso
import NativeOriginalLeftPathActionNaturality
import NativeDaggerUnderlyingIso

/-! Exact Sigma-equivariant right/left reversal on the ORIGINAL dagger coherent nerve. -/
set_option autoImplicit false
open CategoryTheory Opposite Simplicial HomotopicalAlgebra DaggerModels OrdinaryRigidification
open DaggerOriginalDaggerRealizationC2Action DaggerOriginalCompletedDaggerMappingAction
open DaggerOriginalSimplicialGroupoidCompletionUniversal DaggerOriginalStrictDaggerGroupoidSigma
open DaggerOriginalSimplicialDegreeCategory DaggerOriginalSimplicialDaggerDegreeLaws
open DaggerNativeOriginalRealSigmaAnchors DaggerNativeOriginalSigmaLeftPathAction
open DaggerNativeOriginalRightOppositeLeftTransport DaggerNativeOriginalC2RealizationMapping
open DaggerNativeOriginalLeftPathEndpointTransport
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerNativeOriginalSigmaRightLeftReversal
noncomputable section

variable (C : DaggerSimplicialCat.{u, u}) (hC : IsStrictGroupoid C.toSimplicialCat)
variable (x y : Labels C)

def strictSigmaDaggerFunctor : C ⟶ C where
  __ := strictSigmaFunctor C hC
  map_dagger a b := by
    ext n f
    letI := strictDegreeGroupoid C.toSimplicialCat hC n
    change degreeDagger C n (inv (degreeDagger C n f)) =
      inv (degreeDagger C n (degreeDagger C n f))
    rw [degreeDagger_inv C hC n, degreeDagger_involutive]

def nerveDaggerIso : coherentNerve.obj C.toSimplicialCat ≅
    (coherentNerve.obj C.toSimplicialCat).op :=
  DaggerNativeDaggerUnderlyingIso.daggerIso (DaggerNerve.daggerCoherentNerve.obj C)

theorem generator_dagger_comm :
    generatorMap C hC ≫ (nerveDaggerIso C).hom =
      (nerveDaggerIso C).hom ≫ SSet.opFunctor.map (generatorMap C hC) :=
  (DaggerNerve.daggerCoherentNerve.map (strictSigmaDaggerFunctor C hC)).comm

abbrev reversedAction := oppositeLeftAction (generatorMap C hC) (generatorMap_square C hC)
  x y (generatorMap_vertex C hC x) (generatorMap_vertex C hC y)

theorem right_generator_map :
    ((DaggerNativeOriginalSigmaRightConeHomIso.rightAction C hC x y).ρ generator).asHom =
      rightMapTo (generatorMap C hC) x y x y
        (generatorMap_vertex C hC x) (generatorMap_vertex C hC y) := by
  rw [DaggerNativeOriginalSigmaRightConeHomIso.right_generator]
  apply NatTrans.ext
  funext n v
  apply Subtype.ext
  rw [DaggerNativeOriginalRightConeEndpointComparison.postcompTo_raw, rightMapTo_raw]
  rfl

def rightOppositeLeftIso :
    DaggerNativeOriginalSigmaRightConeHomIso.rightAction C hC x y ≅
      reversedAction C hC x y :=
  Action.mkIso (DaggerActualGeneralRightConeKan.comparisonIso
    (coherentNerve.obj C.toSimplicialCat) x y) (by
      intro g
      rcases originalC2_cases g with rfl | rfl
      · rw [MonoidHom.map_one, MonoidHom.map_one]
        change 𝟙 _ ≫ _ = _ ≫ 𝟙 _
        rw [Category.id_comp, Category.comp_id]
      · change ((DaggerNativeOriginalSigmaRightConeHomIso.rightAction C hC x y).ρ
            generator).asHom ≫ _ = _ ≫ ((reversedAction C hC x y).ρ generator).asHom
        rw [right_generator_map, oppositeLeftAction_generator]
        exact comparison_naturalityTo (generatorMap C hC) x y x y
          (generatorMap_vertex C hC x) (generatorMap_vertex C hC y))

def leftDaggerIso : leftAction C hC y x ≅
    innerLeftAction (generatorMap C hC) (generatorMap_square C hC) x y
      (generatorMap_vertex C hC x) (generatorMap_vertex C hC y) :=
  Action.mkIso (DaggerNativePrefixMappingTransportIso.mappingIso (nerveDaggerIso C) ⦋0⦌
    y x (SSet.opObjEquiv.symm y) (SSet.opObjEquiv.symm x)
    (DaggerNativeDaggerUnderlyingIso.vertex (DaggerNerve.daggerCoherentNerve.obj C) y)
    (DaggerNativeDaggerUnderlyingIso.vertex (DaggerNerve.daggerCoherentNerve.obj C) x))
    (by
      intro g
      rcases originalC2_cases g with rfl | rfl
      · rw [MonoidHom.map_one, MonoidHom.map_one]
        change 𝟙 _ ≫ _ = _ ≫ 𝟙 _
        rw [Category.id_comp, Category.comp_id]
      · unfold leftAction innerLeftAction DaggerNativeOriginalLeftPathInvolutionAction.leftAction
        rw [DaggerNativeOriginalC2InvolutionAction.action_generator,
          DaggerNativeOriginalC2InvolutionAction.action_generator]
        exact DaggerNativeOriginalLeftPathActionNaturality.left_comm
          (generatorMap C hC) (SSet.opFunctor.map (generatorMap C hC)) y x
          (SSet.opObjEquiv.symm y) (SSet.opObjEquiv.symm x)
          (generatorMap_vertex C hC y) (generatorMap_vertex C hC x)
          (op_vertex _ y y (generatorMap_vertex C hC y))
          (op_vertex _ x x (generatorMap_vertex C hC x))
          (nerveDaggerIso C).hom (generator_dagger_comm C hC)
          (DaggerNativeDaggerUnderlyingIso.vertex (DaggerNerve.daggerCoherentNerve.obj C) y)
          (DaggerNativeDaggerUnderlyingIso.vertex (DaggerNerve.daggerCoherentNerve.obj C) x))

def rightToOppositeLeftIso :
    DaggerNativeOriginalSigmaRightConeHomIso.rightAction C hC x y ≅
      DaggerNativeOriginalC2RealizationOpposite.oppositeFunctor.obj (leftAction C hC y x) :=
  rightOppositeLeftIso C hC x y ≪≫
    (DaggerNativeOriginalC2RealizationOpposite.oppositeFunctor.mapIso
      (leftDaggerIso C hC x y)).symm

def realizedRightLeftIso :
    mappingFunctor.obj (DaggerNativeOriginalSigmaRightConeHomIso.rightAction C hC x y) ≅
      mappingFunctor.obj (leftAction C hC y x) :=
  mappingFunctor.mapIso (rightToOppositeLeftIso C hC x y) ≪≫
    DaggerNativeOriginalC2RealizationOpposite.mappingIso (leftAction C hC y x)

def rightToReversedPath :
    mappingFunctor.obj (DaggerNativeOriginalSigmaRightConeHomIso.rightAction C hC x y) ⟶
      mappingFunctor.obj (pathAction C hC y x) :=
  (realizedRightLeftIso C hC x y).hom ≫ realizedEC2Comparison C hC y x

theorem rightToReversedPath_weak : WeakEquivalence (rightToReversedPath C hC x y) := by
  have : WeakEquivalence (realizedEC2Comparison C hC y x) :=
    realizedEC2Comparison_weak C hC y x
  unfold rightToReversedPath
  infer_instance

end
end DaggerNativeOriginalSigmaRightLeftReversal
