import NativeOriginalRightConeEndpointComparison
import NativeOriginalStrictHomQSpan
import NativeOriginalSigmaLeftPathAction

/-! The OLD right cone/Q-singular ISO is equivariant for the EXACT original inverse dagger. -/
set_option autoImplicit false
open CategoryTheory Opposite Simplicial HomotopicalAlgebra DaggerModels OrdinaryRigidification
open DaggerOriginalDaggerRealizationC2Action DaggerOriginalCompletedDaggerMappingAction
open DaggerOriginalSimplicialGroupoidCompletionUniversal DaggerOriginalStrictDaggerGroupoidSigma
open DaggerOriginalStrictDaggerGroupoidMappingAction DaggerNativeOriginalC2QSingularSpan
open DaggerNativeOriginalRealSigmaAnchors DaggerNativeOriginalSigmaLeftPathAction
open DaggerNativeOriginalRightConeEndpointComparison
open DaggerOriginalCounitBNextConeEvaluationIndex
open DaggerOriginalCounitBNextConeRealizationFactorization
open DaggerOriginalCounitRightConeQRealizationAdjunction
open DaggerNativeOriginalC2RealizationMapping
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerNativeOriginalSigmaRightConeHomIso
noncomputable section

variable (C : DaggerSimplicialCat.{u, u}) (hC : IsStrictGroupoid C.toSimplicialCat)
variable (x y : Labels C)

def rightMap :
    rightConeSimplices C.toSimplicialCat x y ⟶ rightConeSimplices C.toSimplicialCat x y :=
  postcompTo (strictSigmaFunctor C hC) x y x y
    (generatorMap_vertex C hC x) (generatorMap_vertex C hC y)

def rightEnd : End (rightConeSimplices C.toSimplicialCat x y) := End.of (rightMap C hC x y)

theorem rightEnd_square : rightEnd C hC x y * rightEnd C hC x y = 1 := by
  change rightMap C hC x y ≫ rightMap C hC x y = 𝟙 _
  apply NatTrans.ext
  funext n v
  apply Subtype.ext
  change ((rightMap C hC x y).app n ((rightMap C hC x y).app n v)).val = v.val
  unfold rightMap
  rw [postcompTo_raw, postcompTo_raw]
  change (v.val ≫ generatorMap C hC) ≫ generatorMap C hC = v.val
  rw [Category.assoc, generatorMap_square, Category.comp_id]

def rightAction : Action SSet.{u} C2.{u} :=
  DaggerNativeOriginalC2InvolutionAction.action (rightEnd C hC x y) (rightEnd_square C hC x y)

theorem right_generator :
    ((rightAction C hC x y).ρ generator).asHom =
      postcompTo (strictSigmaFunctor C hC) x y x y
        (generatorMap_vertex C hC x) (generatorMap_vertex C hC y) := by
  unfold rightAction
  rw [DaggerNativeOriginalC2InvolutionAction.action_generator]
  rfl

abbrev homAction := strictMappingAction C hC (label C x) (label C y)

theorem homMapTo_sigma :
    homMapTo (strictSigmaFunctor C hC) x y x y
        (generatorMap_vertex C hC x) (generatorMap_vertex C hC y) =
      strictSigmaHom C hC (label C x) (label C y) := by
  rw [homMapTo_formula]
  simp only [DaggerModels.OriginalOrdinaryMovingHomColimits.castMap,
    DaggerModels.OriginalOrdinaryEndpointTransport.transport, eqToHom_refl, Category.comp_id]
  rfl

theorem singular_generator :
    ((singularAction (homAction C hC x y)).ρ generator).asHom =
      singular.map (strictSigmaHom C hC (label C x) (label C y)) := by
  change singular.map (((strictMappingAction C hC (label C x) (label C y)).ρ generator).asHom) = _
  rw [strictMappingAction_generator]

def comparisonIso : rightAction C hC x y ≅ singularAction (homAction C hC x y) :=
  Action.mkIso (DaggerActualRightConeSingularComparisonIso.comparisonIso C.toSimplicialCat x y)
    (by
      intro g
      rcases originalC2_cases g with rfl | rfl
      · rw [MonoidHom.map_one, MonoidHom.map_one]
        change 𝟙 _ ≫ _ = _ ≫ 𝟙 _
        rw [Category.id_comp, Category.comp_id]
      · change ((rightAction C hC x y).ρ generator).asHom ≫
            coneSingularComparison C.toSimplicialCat x y =
          coneSingularComparison C.toSimplicialCat x y ≫
            ((singularAction (homAction C hC x y)).ρ generator).asHom
        rw [right_generator, singular_generator]
        have h := comparison_naturalityTo (strictSigmaFunctor C hC) x y x y
          (generatorMap_vertex C hC x) (generatorMap_vertex C hC y)
        rw [homMapTo_sigma] at h
        exact h)

def realizedIso :
    mappingFunctor.obj (rightAction C hC x y) ≅
      mappingFunctor.obj (singularAction (homAction C hC x y)) :=
  mappingFunctor.mapIso (comparisonIso C hC x y)

def rightConeToMixed :
    mappingFunctor.obj (rightAction C hC x y) ⟶
      mappingFunctor.obj (mixedAction (homAction C hC x y)) :=
  (realizedIso C hC x y).hom ≫ realizedSingularComparison (homAction C hC x y)

theorem both_realized_weak :
    WeakEquivalence (realizedConstants (homAction C hC x y)) ∧
      WeakEquivalence (rightConeToMixed C hC x y) := by
  have h := DaggerNativeOriginalStrictHomQSpan.both_realized_EC2_weak
    C hC (label C x) (label C y)
  have : WeakEquivalence (realizedSingularComparison (homAction C hC x y)) := h.2
  refine ⟨h.1, ?_⟩
  unfold rightConeToMixed
  infer_instance

end
end DaggerNativeOriginalSigmaRightConeHomIso
