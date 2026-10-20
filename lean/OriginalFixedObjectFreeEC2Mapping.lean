import OriginalFixedObjectFreeDaggerMappingComparison
import OriginalFreeEC2DaggerGroupoidComparison
import OriginalStrictDaggerGroupoidDerivedMapping

/-!
# The actual free EC2 dagger groupoid represents the original equivariant mapping

Identify the original evaluation action with the previously verified strict Hom
action, keeping the identity on its entire underlying simplicial set. Specialize
the full native free mapping isomorphism to the original EC2 action. The source is
cofibrant and its map to the free point is a weak equivalence by the proved actual
model. The paper interval and ambient derived mapping comparison remain separate.
-/
set_option autoImplicit false
open CategoryTheory MonoidalCategory DaggerModels
open DaggerOriginalFixedObjectDaggerCategories DaggerOriginalFixedObjectOrdinaryCellAdjunction
open DaggerOriginalFixedObjectFreeDaggerGroupoidQuillen
open DaggerOriginalFixedObjectFreeDaggerMappingComparison
open DaggerOriginalFreeEC2DaggerGroupoidComparison
open DaggerOriginalDaggerRealizationC2Action DaggerOriginalEC2SimplicialAction
open DaggerOriginalCompletedDaggerMappingAction
open DaggerOriginalStrictDaggerGroupoidMappingAction
open DaggerOriginalStrictDaggerGroupoidDerivedMapping
open DaggerOriginalSimplicialEquivariantEnrichedAdjunction
universe u
namespace DaggerOriginalFixedObjectFreeEC2Mapping
noncomputable section

/-- The full evaluation action is the original strict Hom action via the identity Hom map. -/
def evaluationOriginalActionIso (C : FixedStrictDaggerGroupoids TwoObjects.{u}) :
    daggerEvaluation.obj C ≅ strictMappingAction (originalDagger C.obj) C.property
      TwoObjectDaggerGraph.left TwoObjectDaggerGraph.right where
  hom :=
    { hom := 𝟙 _
      comm g := by
        rcases originalC2_cases g with rfl | rfl
        · simp
        · simp only [Category.comp_id, Category.id_comp]
          change ((daggerEvaluation.obj C).ρ generator).asHom =
            ((strictMappingAction (originalDagger C.obj) C.property
              TwoObjectDaggerGraph.left TwoObjectDaggerGraph.right).ρ generator).asHom
          rw [daggerEvaluation_generator, strictMappingAction_generator] }
  inv :=
    { hom := 𝟙 _
      comm g := by
        rcases originalC2_cases g with rfl | rfl
        · simp
        · simp only [Category.comp_id, Category.id_comp]
          change ((strictMappingAction (originalDagger C.obj) C.property
            TwoObjectDaggerGraph.left TwoObjectDaggerGraph.right).ρ generator).asHom =
              ((daggerEvaluation.obj C).ρ generator).asHom
          rw [daggerEvaluation_generator, strictMappingAction_generator] }
  hom_inv_id := Action.Hom.ext (Category.id_comp _)
  inv_hom_id := Action.Hom.ext (Category.id_comp _)

/-- The comparison keeps the whole original Hom simplicial set literally unchanged. -/
theorem evaluationOriginalActionIso_hom (C : FixedStrictDaggerGroupoids TwoObjects.{u}) :
    (evaluationOriginalActionIso C).hom.hom = 𝟙 _ := rfl

/-- The free original EC2 has the paper's full original equivariant Hom mapping object. -/
def freeEC2MappingIso (C : FixedStrictDaggerGroupoids TwoObjects.{u}) :
    (freeEC2 ⟶[SSet.{u}] C) ≅ strictDerivedMapping (originalDagger C.obj) C.property
      TwoObjectDaggerGraph.left TwoObjectDaggerGraph.right :=
  freeDaggerMappingIso simplicialAction C ≪≫
    (enrichedMappingFunctor simplicialAction).mapIso (evaluationOriginalActionIso C)

end
end DaggerOriginalFixedObjectFreeEC2Mapping
