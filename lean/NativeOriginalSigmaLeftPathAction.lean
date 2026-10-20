import NativeOriginalLeftPathInvolutionAction
import NativeOriginalRealSigmaUnitaryEndpoint

/-! Instantiate with the EXACT OLD inverse-dagger Sigma on the SAME original coherent nerve. -/
set_option autoImplicit false
open CategoryTheory Opposite Simplicial HomotopicalAlgebra DaggerModels OrdinaryRigidification
open DaggerOriginalSimplicialGroupoidCompletionUniversal DaggerOriginalStrictDaggerGroupoidSigma
open DaggerNativeOriginalRealSigmaAnchors DaggerNativeOriginalFunctorInvolutionAction
open DaggerOriginalDaggerRealizationC2Action
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerNativeOriginalSigmaLeftPathAction
noncomputable section

variable (C : DaggerSimplicialCat.{u, u}) (hC : IsStrictGroupoid C.toSimplicialCat)

def generatorMap : coherentNerve.obj C.toSimplicialCat ⟶ coherentNerve.obj C.toSimplicialCat :=
  coherentNerve.map (strictSigmaFunctor C hC)

theorem generatorMap_square : generatorMap C hC ≫ generatorMap C hC = 𝟙 _ := by
  unfold generatorMap
  rw [← coherentNerve.map_comp, strictSigmaFunctor_involutive, coherentNerve.map_id]

theorem generatorMap_eq_original : generatorMap C hC = ((node0 C hC).ρ generator).asHom :=
  (DaggerNativeOriginalFunctorInvolutionAction.action_generator coherentNerve
    (strictSigmaFunctor C hC) (strictSigmaFunctor_involutive C hC)).symm

theorem generatorMap_vertex (x : Labels C) : (generatorMap C hC).app (op ⦋0⦌) x = x := by
  rw [generatorMap_eq_original]
  exact fixed0 C hC x generator

def leftAction (x y : Labels C) : Action SSet.{u} C2.{u} :=
  DaggerNativeOriginalLeftPathInvolutionAction.leftAction
    (generatorMap C hC) (generatorMap_square C hC) x y
    (generatorMap_vertex C hC x) (generatorMap_vertex C hC y)

def pathAction (x y : Labels C) : Action SSet.{u} C2.{u} :=
  DaggerNativeOriginalLeftPathInvolutionAction.pathAction
    (generatorMap C hC) (generatorMap_square C hC) x y
    (generatorMap_vertex C hC x) (generatorMap_vertex C hC y)

def comparison (x y : Labels C) : leftAction C hC x y ⟶ pathAction C hC x y :=
  DaggerNativeOriginalLeftPathInvolutionAction.comparisonAction
    (generatorMap C hC) (generatorMap_square C hC) x y
    (generatorMap_vertex C hC x) (generatorMap_vertex C hC y)

/-- Strictness supplies the SAME native Kan input, without adding a local Kan hypothesis. -/
theorem comparison_weak (x y : Labels C) : WeakEquivalence (comparison C hC x y).hom := by
  have : (coherentNerve.obj C.toSimplicialCat).KanComplex :=
    DaggerNativeOriginalRealSigmaUnitaryEndpoint.nerve_kan C hC
  exact DaggerNativeOriginalLeftPathInvolutionAction.comparisonAction_weak _ _ _ _ _ _

def realizedEC2Comparison (x y : Labels C) :
    DaggerNativeOriginalC2RealizationMapping.mappingFunctor.obj (leftAction C hC x y) ⟶
      DaggerNativeOriginalC2RealizationMapping.mappingFunctor.obj (pathAction C hC x y) :=
  DaggerNativeOriginalC2RealizationMapping.mappingFunctor.map (comparison C hC x y)

theorem realizedEC2Comparison_weak (x y : Labels C) :
    WeakEquivalence (realizedEC2Comparison C hC x y) := by
  have : WeakEquivalence (comparison C hC x y).hom := comparison_weak C hC x y
  exact DaggerNativeOriginalC2RealizationMapping.mapping_map_weak _

end
end DaggerNativeOriginalSigmaLeftPathAction
