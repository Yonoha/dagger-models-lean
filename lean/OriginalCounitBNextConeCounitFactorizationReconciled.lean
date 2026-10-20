import OriginalCounitBNextConeEvaluationNaturalityReconciled

/-!
# The original counit factors the right-cone evaluation cocone

The first cocone has apex the actual Hom in `C.obj (N.obj D)`. Postcomposing
its legs with the original counit Hom map, including both object transports,
gives the previously defined right-cone evaluation cocone. No colimit or
weak-equivalence comparison is asserted.
-/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite Simplicial EnrichedCategory
open DaggerModels DaggerChosenRigidificationNecklace
open DaggerModels.OriginalOrdinaryMovingHomColimits
open DaggerOriginalCounitRightCone DaggerOriginalCounitRightConeFunctor
open DaggerOriginalCounitRightConeQFunctor
open DaggerOriginalCounitBNextConeEvaluationIndex
open DaggerOriginalCounitBNextConeEvaluationNaturality

universe u

namespace DaggerOriginalCounitBNextConeCounitFactorization

noncomputable section

private abbrev C := OrdinaryRigidification.rigidification.{u}
private abbrev N := OrdinaryRigidification.coherentNerve.{u}
private abbrev A := OrdinaryRigidification.rigidificationCoherentNerveAdjunction.{u}
private abbrev RV := OrdinaryRigidification.RigidificationVertices.vertexEquiv.{u}

private def rigidAlpha (D : SimplicialCat.{u, u})
    (v w : (N.obj D).obj (op ⦋0⦌)) (n : ℕ)
    (σ : (rightConeSimplices D v w).obj (op ⦋n⦌)) :
    (C.map σ.1).obj (alphaObj.{u} n) = RV (N.obj D) v :=
  (OrdinaryRigidification.RigidificationVertices.vertexEquiv_naturality
    σ.1 (alpha.{u} n)).trans (congrArg (RV (N.obj D)) σ.2.1)

private def rigidOmega (D : SimplicialCat.{u, u})
    (v w : (N.obj D).obj (op ⦋0⦌)) (n : ℕ)
    (σ : (rightConeSimplices D v w).obj (op ⦋n⦌)) :
    (C.map σ.1).obj (omegaObj.{u} n) = RV (N.obj D) w :=
  (OrdinaryRigidification.RigidificationVertices.vertexEquiv_naturality
    σ.1 (omega.{u} n)).trans (congrArg (RV (N.obj D)) σ.2.2)

/-- The original rigidification Hom leg of a supplied right-cone simplex. -/
def rightConeRigidificationLeg (D : SimplicialCat.{u, u})
    (v w : (N.obj D).obj (op ⦋0⦌)) (n : ℕ)
    (σ : (rightConeSimplices D v w).obj (op ⦋n⦌)) :
    Q.{u} n ⟶ (C.obj (N.obj D)).enriched.Hom
      (RV (N.obj D) v) (RV (N.obj D) w) :=
  castMap (C.map σ.1) (alphaObj.{u} n) (omegaObj.{u} n)
    (RV (N.obj D) v) (RV (N.obj D) w)
    (rigidAlpha D v w n σ) (rigidOmega D v w n σ)

/-- Every operator respects the literal rigidification Hom legs. -/
theorem rightConeRigidificationLeg_naturality (D : SimplicialCat.{u, u})
    (v w : (N.obj D).obj (op ⦋0⦌)) {m n : SimplexCategory}
    (f : m ⟶ n) (τ : (rightConeSimplices D v w).obj (op n)) :
    Qmap.{u} f ≫ rightConeRigidificationLeg D v w n.len τ =
      rightConeRigidificationLeg D v w m.len
        ((rightConeSimplices D v w).map f.op τ) := by
  change castMap (C.map (coneMap.{u} f))
      (alphaObj.{u} m.len) (omegaObj.{u} m.len)
      (alphaObj.{u} n.len) (omegaObj.{u} n.len)
      (sourceObject_map.{u} f) (targetObject_map.{u} f) ≫
      castMap (C.map τ.1) (alphaObj.{u} n.len) (omegaObj.{u} n.len)
        _ _ (rigidAlpha D v w n.len τ) (rigidOmega D v w n.len τ) =
    castMap (C.map (coneMap.{u} f ≫ τ.1))
      (alphaObj.{u} m.len) (omegaObj.{u} m.len) _ _ _ _
  rw [← castMap_comp (C.map (coneMap.{u} f)) (C.map τ.1)
    (alphaObj.{u} m.len) (omegaObj.{u} m.len)
    (alphaObj.{u} n.len) (omegaObj.{u} n.len) _ _
    (sourceObject_map.{u} f) (targetObject_map.{u} f)
    (rigidAlpha D v w n.len τ) (rigidOmega D v w n.len τ)]
  exact castMap_congr (C.map_comp (coneMap.{u} f) τ.1).symm
    (alphaObj.{u} m.len) (omegaObj.{u} m.len) _ _ _ _ _ _

/-- Natural transformation of original rigidification Hom legs. -/
def rightConeRigidificationNatTrans (D : SimplicialCat.{u, u})
    (v w : (N.obj D).obj (op ⦋0⦌)) :
    rightConeWeight D v w ⟶
      (Functor.const _).obj
        ((C.obj (N.obj D)).enriched.Hom (RV (N.obj D) v) (RV (N.obj D) w)) where
  app σ := rightConeRigidificationLeg D v w σ.left.len (uliftYonedaEquiv σ.hom)
  naturality σ τ f := by
    have hsimplex :
        (rightConeSimplices D v w).map f.left.op
            (uliftYonedaEquiv τ.hom) = uliftYonedaEquiv σ.hom := by
      simpa only [Quiver.Hom.unop_op, CostructuredArrow.w f] using
        (uliftYonedaEquiv_naturality (F := rightConeSimplices D v w)
          τ.hom f.left.op)
    change Qmap.{u} f.left ≫
        rightConeRigidificationLeg D v w τ.left.len (uliftYonedaEquiv τ.hom) =
      rightConeRigidificationLeg D v w σ.left.len (uliftYonedaEquiv σ.hom)
    exact (rightConeRigidificationLeg_naturality D v w f.left
      (uliftYonedaEquiv τ.hom)).trans
        (congrArg (rightConeRigidificationLeg D v w σ.left.len) hsimplex)

/-- The actual Hom cocone in `C.obj (N.obj D)`, with both original RV labels. -/
def rightConeRigidificationCocone (D : SimplicialCat.{u, u})
    (v w : (N.obj D).obj (op ⦋0⦌)) :
    Cocone (rightConeWeight D v w) where
  pt := (C.obj (N.obj D)).enriched.Hom (RV (N.obj D) v) (RV (N.obj D) w)
  ι := rightConeRigidificationNatTrans D v w

/-- The precise Hom component of the existing original adjunction counit. -/
def counitHom (D : SimplicialCat.{u, u})
    (v w : (N.obj D).obj (op ⦋0⦌)) :
    (C.obj (N.obj D)).enriched.Hom (RV (N.obj D) v) (RV (N.obj D) w) ⟶
      D.enriched.Hom
        (OrdinaryRigidification.NerveVertices.vertexEquiv D v)
        (OrdinaryRigidification.NerveVertices.vertexEquiv D w) :=
  castMap (A.counit.app D) (RV (N.obj D) v) (RV (N.obj D) w)
    (OrdinaryRigidification.NerveVertices.vertexEquiv D v)
    (OrdinaryRigidification.NerveVertices.vertexEquiv D w)
    (DaggerOriginalCounitObjects.counit_obj_vertex D v)
    (DaggerOriginalCounitObjects.counit_obj_vertex D w)

/-- Every original evaluation is the rigidification leg followed by the same counit. -/
theorem rightConeEvaluation_factor (D : SimplicialCat.{u, u})
    (v w : (N.obj D).obj (op ⦋0⦌)) (n : ℕ)
    (σ : (rightConeSimplices D v w).obj (op ⦋n⦌)) :
    rightConeRigidificationLeg D v w n σ ≫ counitHom D v w =
      rightConeEvaluation D v w n σ := by
  calc
    rightConeRigidificationLeg D v w n σ ≫ counitHom D v w =
        castMap (C.map σ.1 ≫ A.counit.app D)
          (alphaObj.{u} n) (omegaObj.{u} n)
          (OrdinaryRigidification.NerveVertices.vertexEquiv D v)
          (OrdinaryRigidification.NerveVertices.vertexEquiv D w)
          ((congrArg (A.counit.app D).obj (rigidAlpha D v w n σ)).trans
            (DaggerOriginalCounitObjects.counit_obj_vertex D v))
          ((congrArg (A.counit.app D).obj (rigidOmega D v w n σ)).trans
            (DaggerOriginalCounitObjects.counit_obj_vertex D w)) :=
      (castMap_comp (C.map σ.1) (A.counit.app D)
        (alphaObj.{u} n) (omegaObj.{u} n)
        (RV (N.obj D) v) (RV (N.obj D) w)
        (OrdinaryRigidification.NerveVertices.vertexEquiv D v)
        (OrdinaryRigidification.NerveVertices.vertexEquiv D w)
        (rigidAlpha D v w n σ) (rigidOmega D v w n σ)
        (DaggerOriginalCounitObjects.counit_obj_vertex D v)
        (DaggerOriginalCounitObjects.counit_obj_vertex D w)).symm
    _ = rightConeEvaluation D v w n σ := by
      simp only [rightConeEvaluation, DaggerOriginalCounitRightCone.evaluation,
        castMap, OriginalOrdinaryEndpointTransport.transport,
        SimplicialCat.comp_map, Category.assoc, targetHomTransport,
        eqToHom_trans]

/-- The two natural transformations agree after the literal counit Hom map. -/
theorem rightConeEvaluationNatTrans_factor (D : SimplicialCat.{u, u})
    (v w : (N.obj D).obj (op ⦋0⦌)) :
    rightConeRigidificationNatTrans D v w ≫
      (Functor.const _).map (counitHom D v w) =
        rightConeEvaluationNatTrans D v w := by
  apply NatTrans.ext
  funext σ
  exact rightConeEvaluation_factor D v w σ.left.len (uliftYonedaEquiv σ.hom)

/-- The whole evaluation cocone is postcomposition with the original counit. -/
theorem rightConeEvaluationCocone_factor (D : SimplicialCat.{u, u})
    (v w : (N.obj D).obj (op ⦋0⦌)) :
    (rightConeRigidificationCocone D v w).extend (counitHom D v w) =
      rightConeEvaluationCocone D v w := by
  have hι :
      ((rightConeRigidificationCocone D v w).extend (counitHom D v w)).ι =
        (rightConeEvaluationCocone D v w).ι := by
    exact rightConeEvaluationNatTrans_factor D v w
  exact congrArg (fun ι ↦ (⟨_, ι⟩ : Cocone (rightConeWeight D v w))) hι

end

end DaggerOriginalCounitBNextConeCounitFactorization
