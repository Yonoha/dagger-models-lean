import OriginalWalkingIsoNerveComparison
import OriginalWalkingIsoCoherentObstructionReconciled
import OriginalCounitObjects

/-!
# The original walking-isomorphism counit with zero integer labels

This is the actual ordinary rigidification/coherent-nerve transpose. The source
is the actual codiscrete enrichment of the walking isomorphism, and the target
is the ordinary constant-Hom enrichment of the existing integer dagger groupoid.
The ordinary zero-labelled map is not asserted to preserve a dagger.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial DaggerModels
open DaggerUnitaryDiscrete
open DaggerModels.OrdinaryRigidification
open DaggerModels.OriginalWalkingIsoIntegerObstruction
open DaggerModels.OriginalWalkingIsoNerveComparison

universe u

namespace DaggerModels.OriginalWalkingIsoCounitIntegerMap

noncomputable section

private abbrev C : SSet.{u} ⥤ SimplicialCat.{u, u} :=
  OrdinaryRigidification.rigidification

private abbrev N : SimplicialCat.{u, u} ⥤ SSet.{u} :=
  OrdinaryRigidification.coherentNerve

private abbrev A : C.{u} ⊣ N.{u} :=
  OrdinaryRigidification.rigidificationCoherentNerveAdjunction

private abbrev D : SimplicialCat.{u, u} :=
  (ordinaryEnrichment integerTarget.{u}).toSimplicialCat

/-- The image of the unique ordinary walking arrow between any two objects. -/
def zeroArrow (x y : walkingIso.{u}) :
    walkingToInteger.{u}.obj x ⟶ walkingToInteger.{u}.obj y :=
  walkingToInteger.{u}.map (show x ⟶ y from ⟨⟨⟩⟩)

/-- Every simplex in the terminal source Hom receives the actual zero label. -/
def zeroHom (x y : walkingIso.{u}) :
    (walkingSimplicial.{u}.enriched.Hom x y) ⟶
      (D.{u}.enriched.Hom (walkingToInteger.{u}.obj x)
        (walkingToInteger.{u}.obj y)) where
  app _ _ := zeroArrow x y
  naturality _ _ _ := rfl

/-- The ordinary zero-labelled walking functor, with both original endpoints. -/
def walkingZeroEnriched : walkingSimplicial.{u} ⟶ D.{u} where
  obj := walkingToInteger.{u}.obj
  map := zeroHom
  map_id x := by
    ext n p
    rfl
  map_comp x y z := by
    ext n p
    rfl

/-- Its object function is exactly the original ordinary functor's object map. -/
theorem walkingZeroEnriched_obj (x : walkingIso.{u}) :
    walkingZeroEnriched.{u}.obj x = walkingToInteger.{u}.obj x := rfl

/-- The ordinary nerve maps through the actual codiscrete coherent nerve. -/
def nerveZeroMap : nerve walkingIso.{u} ⟶ N.{u}.obj D.{u} :=
  comparisonIso.{u}.hom ≫ N.{u}.map walkingZeroEnriched.{u}

/-- The map from the original ordinary rigidification is the adjoint transpose. -/
def counitToInteger : C.{u}.obj (nerve walkingIso.{u}) ⟶ D.{u} :=
  (A.{u}.homEquiv (nerve walkingIso.{u}) D.{u}).symm nerveZeroMap.{u}

/-- The transpose is the original counit after the original nerve map. -/
theorem counitToInteger_mate :
    C.{u}.map nerveZeroMap.{u} ≫ A.{u}.counit.app D.{u} =
      counitToInteger.{u} :=
  (A.{u}.homEquiv_counit (g := nerveZeroMap.{u})).symm

/-- A source vertex is sent to its original zero-labelled target object. -/
theorem counitToInteger_vertex (x : walkingIso.{u}) :
    counitToInteger.{u}.obj
      (RigidificationVertices.vertexEquiv (nerve walkingIso.{u})
        (ComposableArrows.mk₀ x)) = walkingToInteger.{u}.obj x := by
  let v : (nerve walkingIso.{u}).obj (op ⦋0⦌) := ComposableArrows.mk₀ x
  let P := (comparisonIso.{u}.hom).app (op ⦋0⦌) v
  have hp : NerveVertices.vertexEquiv walkingSimplicial.{u} P = x := by
    rw [NerveVertices.vertexEquiv_apply]
    exact comparison_zero x
  calc
    counitToInteger.{u}.obj
        (RigidificationVertices.vertexEquiv (nerve walkingIso.{u}) v) =
      (A.{u}.counit.app D.{u}).obj
        ((C.{u}.map nerveZeroMap.{u}).obj
          (RigidificationVertices.vertexEquiv (nerve walkingIso.{u}) v)) := by
            rw [← counitToInteger_mate]
            rfl
    _ = (A.{u}.counit.app D.{u}).obj
          (RigidificationVertices.vertexEquiv (N.{u}.obj D.{u})
            (nerveZeroMap.{u}.app (op ⦋0⦌) v)) := by
            rw [RigidificationVertices.vertexEquiv_naturality]
    _ = NerveVertices.vertexEquiv D.{u}
          (nerveZeroMap.{u}.app (op ⦋0⦌) v) :=
      DaggerOriginalCounitObjects.counit_obj_vertex D.{u} _
    _ = walkingZeroEnriched.{u}.obj
          (NerveVertices.vertexEquiv walkingSimplicial.{u} P) := by
            exact NerveVertices.vertexEquiv_naturality walkingZeroEnriched.{u} P
    _ = walkingToInteger.{u}.obj x := by rw [hp]; rfl

/-- The chosen zero endpoint has its exact original integer target. -/
theorem counitToInteger_zero :
    counitToInteger.{u}.obj
      (RigidificationVertices.vertexEquiv (nerve walkingIso.{u})
        (ComposableArrows.mk₀ walkingZero.{u})) = integerZero.{u} := by
  rw [counitToInteger_vertex, walkingToInteger_zero]

/-- The chosen one endpoint has its exact original integer target. -/
theorem counitToInteger_one :
    counitToInteger.{u}.obj
      (RigidificationVertices.vertexEquiv (nerve walkingIso.{u})
        (ComposableArrows.mk₀ walkingOne.{u})) = integerOne.{u} := by
  rw [counitToInteger_vertex, walkingToInteger_one]

end

end DaggerModels.OriginalWalkingIsoCounitIntegerMap
