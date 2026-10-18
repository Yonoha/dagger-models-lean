import OriginalCounitBNextConeEvaluationIndexReconciled

/-!
# Naturality of the original right-cone counit evaluations

These maps use the literal cone simplex index and the original counit.
The result is a cocone of simplicial sets. No claim about its colimit or
about geometric weak equivalences is made here.
-/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite Simplicial EnrichedCategory
open DaggerModels DaggerChosenRigidificationNecklace
open DaggerModels.OriginalOrdinaryMovingHomColimits
open DaggerOriginalCounitRightCone DaggerOriginalCounitRightConeFunctor
open DaggerOriginalCounitRightConeQFunctor
open DaggerOriginalCounitBNextConeEvaluationIndex

universe u

namespace DaggerOriginalCounitBNextConeEvaluationNaturality

noncomputable section

private abbrev C := OrdinaryRigidification.rigidification.{u}
private abbrev N := OrdinaryRigidification.coherentNerve.{u}
private abbrev A := OrdinaryRigidification.rigidificationCoherentNerveAdjunction.{u}

private def fixedAlpha (D : SimplicialCat.{u, u})
    (v w : (N.obj D).obj (op ⦋0⦌)) (n : ℕ)
    (σ : (rightConeSimplices D v w).obj (op ⦋n⦌)) :
    (C.map σ.1 ≫ A.counit.app D).obj (alphaObj.{u} n) =
      OrdinaryRigidification.NerveVertices.vertexEquiv D v :=
  (evaluation_alpha_obj.{u} D n σ.1).trans
    (congrArg (OrdinaryRigidification.NerveVertices.vertexEquiv D) σ.2.1)

private def fixedOmega (D : SimplicialCat.{u, u})
    (v w : (N.obj D).obj (op ⦋0⦌)) (n : ℕ)
    (σ : (rightConeSimplices D v w).obj (op ⦋n⦌)) :
    (C.map σ.1 ≫ A.counit.app D).obj (omegaObj.{u} n) =
      OrdinaryRigidification.NerveVertices.vertexEquiv D w :=
  (evaluation_omega_obj.{u} D n σ.1).trans
    (congrArg (OrdinaryRigidification.NerveVertices.vertexEquiv D) σ.2.2)

private theorem evaluation_castMap (D : SimplicialCat.{u, u})
    (v w : (N.obj D).obj (op ⦋0⦌)) (n : ℕ)
    (σ : (rightConeSimplices D v w).obj (op ⦋n⦌)) :
    rightConeEvaluation D v w n σ =
      castMap (C.map σ.1 ≫ A.counit.app D)
        (alphaObj.{u} n) (omegaObj.{u} n)
        (OrdinaryRigidification.NerveVertices.vertexEquiv D v)
        (OrdinaryRigidification.NerveVertices.vertexEquiv D w)
        (fixedAlpha D v w n σ) (fixedOmega D v w n σ) := by
  simp only [rightConeEvaluation, DaggerOriginalCounitRightCone.evaluation, castMap,
    OriginalOrdinaryEndpointTransport.transport, SimplicialCat.comp_map,
    Category.assoc, targetHomTransport, eqToHom_trans]

/-- Every actual simplex operator commutes with the original counit evaluation. -/
theorem rightConeEvaluation_naturality (D : SimplicialCat.{u, u})
    (v w : (N.obj D).obj (op ⦋0⦌)) {m n : SimplexCategory}
    (f : m ⟶ n) (τ : (rightConeSimplices D v w).obj (op n)) :
    Qmap.{u} f ≫ rightConeEvaluation D v w n.len τ =
      rightConeEvaluation D v w m.len
        ((rightConeSimplices D v w).map f.op τ) := by
  rw [evaluation_castMap D v w n.len τ,
    evaluation_castMap D v w m.len ((rightConeSimplices D v w).map f.op τ)]
  change castMap (C.map (coneMap.{u} f))
      (alphaObj.{u} m.len) (omegaObj.{u} m.len)
      (alphaObj.{u} n.len) (omegaObj.{u} n.len)
      (sourceObject_map.{u} f) (targetObject_map.{u} f) ≫
      castMap (C.map τ.1 ≫ A.counit.app D)
        (alphaObj.{u} n.len) (omegaObj.{u} n.len)
        _ _ (fixedAlpha D v w n.len τ) (fixedOmega D v w n.len τ) =
    castMap (C.map (coneMap.{u} f ≫ τ.1) ≫ A.counit.app D)
      (alphaObj.{u} m.len) (omegaObj.{u} m.len)
      _ _ _ _
  rw [← castMap_comp (C.map (coneMap.{u} f))
    (C.map τ.1 ≫ A.counit.app D)
    (alphaObj.{u} m.len) (omegaObj.{u} m.len)
    (alphaObj.{u} n.len) (omegaObj.{u} n.len) _ _
    (sourceObject_map.{u} f) (targetObject_map.{u} f)
    (fixedAlpha D v w n.len τ) (fixedOmega D v w n.len τ)]
  have hfunctor :
      C.map (coneMap.{u} f) ≫ (C.map τ.1 ≫ A.counit.app D) =
        C.map (coneMap.{u} f ≫ τ.1) ≫ A.counit.app D := by
    rw [← Category.assoc, ← C.map_comp]
  exact castMap_congr hfunctor
    (alphaObj.{u} m.len) (omegaObj.{u} m.len) _ _ _ _ _ _

/-- The literal evaluation components form a natural transformation. -/
def rightConeEvaluationNatTrans (D : SimplicialCat.{u, u})
    (v w : (N.obj D).obj (op ⦋0⦌)) :
    rightConeWeight D v w ⟶
      (Functor.const _).obj
        (D.enriched.Hom
          (OrdinaryRigidification.NerveVertices.vertexEquiv D v)
          (OrdinaryRigidification.NerveVertices.vertexEquiv D w)) where
  app σ := rightConeEvaluation D v w σ.left.len
    (uliftYonedaEquiv σ.hom)
  naturality σ τ f := by
    have hsimplex :
        (rightConeSimplices D v w).map f.left.op
            (uliftYonedaEquiv τ.hom) = uliftYonedaEquiv σ.hom := by
      simpa only [Quiver.Hom.unop_op, CostructuredArrow.w f] using
        (uliftYonedaEquiv_naturality (F := rightConeSimplices D v w) τ.hom f.left.op)
    change Qmap.{u} f.left ≫
        rightConeEvaluation D v w τ.left.len (uliftYonedaEquiv τ.hom) =
      rightConeEvaluation D v w σ.left.len (uliftYonedaEquiv σ.hom)
    exact (rightConeEvaluation_naturality D v w f.left (uliftYonedaEquiv τ.hom)).trans
      (congrArg (rightConeEvaluation D v w σ.left.len) hsimplex)

/-- The same natural transformation as a cocone with fixed original Hom apex. -/
def rightConeEvaluationCocone (D : SimplicialCat.{u, u})
    (v w : (N.obj D).obj (op ⦋0⦌)) :
    Cocone (rightConeWeight D v w) where
  pt := D.enriched.Hom
    (OrdinaryRigidification.NerveVertices.vertexEquiv D v)
    (OrdinaryRigidification.NerveVertices.vertexEquiv D w)
  ι := rightConeEvaluationNatTrans D v w

/-- Each cocone leg is the original counit evaluation of that cone simplex. -/
theorem rightConeEvaluationCocone_leg (D : SimplicialCat.{u, u})
    (v w : (N.obj D).obj (op ⦋0⦌))
    (σ : SimplexIndex (rightConeSimplices D v w)) :
    (rightConeEvaluationCocone D v w).ι.app σ =
      rightConeEvaluation D v w σ.left.len (uliftYonedaEquiv σ.hom) := rfl

end

end DaggerOriginalCounitBNextConeEvaluationNaturality
