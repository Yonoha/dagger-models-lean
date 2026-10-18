import OriginalCounitRightConeQFunctorReconciled
import OriginalCounitRightCone
import ChosenRigidificationSimplexColimit

/-!
# BNext: the actual right-cone simplex index for the original counit

For fixed original nerve vertices, the right-cone maps with those endpoints
form a simplicial set under precomposition by the literal cone functor. The
actual `QFunctor` supplies a diagram over its simplex category. Each right-
cone simplex has the original counit evaluation map, with both endpoint casts.
This file does not claim a Reedy or homotopical-colimit comparison.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial EnrichedCategory
open DaggerModels DaggerChosenRigidificationNecklace
open DaggerOriginalEnrichedHomTransport
open DaggerOriginalCounitRightCone DaggerOriginalCounitRightConeFunctor
open DaggerOriginalCounitRightConeQFunctor

universe u

namespace DaggerOriginalCounitBNextConeEvaluationIndex

noncomputable section

private abbrev N := DaggerModels.OrdinaryRigidification.coherentNerve.{u}

/-- Literal right-cone simplices with the two original endpoint values fixed. -/
def rightConeSimplices (D : SimplicialCat.{u, u})
    (v w : (N.obj D).obj (op ⦋0⦌)) : SSet.{u} where
  obj q := {σ : cone.{u} q.unop.len ⟶ N.obj D //
    σ.app (op ⦋0⦌) (alpha.{u} q.unop.len) = v ∧
      σ.app (op ⦋0⦌) (omega.{u} q.unop.len) = w}
  map {q r} f σ := ⟨coneMap.{u} f.unop ≫ σ.1, by
    constructor
    · calc
        (coneMap.{u} f.unop ≫ σ.1).app (op ⦋0⦌) (alpha.{u} r.unop.len) =
            σ.1.app (op ⦋0⦌)
              ((coneMap.{u} f.unop).app (op ⦋0⦌) (alpha.{u} r.unop.len)) := rfl
        _ = σ.1.app (op ⦋0⦌) (alpha.{u} q.unop.len) :=
          congrArg (σ.1.app (op ⦋0⦌)) (alpha_naturality.{u} f.unop)
        _ = v := σ.2.1
    · calc
        (coneMap.{u} f.unop ≫ σ.1).app (op ⦋0⦌) (omega.{u} r.unop.len) =
            σ.1.app (op ⦋0⦌)
              ((coneMap.{u} f.unop).app (op ⦋0⦌) (omega.{u} r.unop.len)) := rfl
        _ = σ.1.app (op ⦋0⦌) (omega.{u} q.unop.len) :=
          congrArg (σ.1.app (op ⦋0⦌)) (omega_naturality.{u} f.unop)
        _ = w := σ.2.2⟩
  map_id q := by
    funext σ
    apply Subtype.ext
    change coneMap.{u} (𝟙 q.unop) ≫ σ.1 = σ.1
    rw [show coneMap.{u} (𝟙 q.unop) = 𝟙 (cone.{u} q.unop.len) from
      coneFunctor.{u}.map_id q.unop]
    exact Category.id_comp _
  map_comp {q r s} f g := by
    funext σ
    apply Subtype.ext
    change coneMap.{u} (g.unop ≫ f.unop) ≫ σ.1 =
      (coneMap.{u} g.unop ≫ coneMap.{u} f.unop) ≫ σ.1
    exact congrArg (fun h => h ≫ σ.1) (coneFunctor.{u}.map_comp g.unop f.unop)

/-- Restriction along an actual simplex operator is precomposition by `coneMap`. -/
theorem rightConeSimplices_map (D : SimplicialCat.{u, u})
    (v w : (N.obj D).obj (op ⦋0⦌)) {q r : SimplexCategoryᵒᵖ}
    (f : q ⟶ r) (σ : (rightConeSimplices.{u} D v w).obj q) :
    ((rightConeSimplices.{u} D v w).map f σ).1 =
      coneMap.{u} f.unop ≫ σ.1 := rfl

/-- The literal `QFunctor`, indexed by actual right-cone simplices. -/
def rightConeWeight (D : SimplicialCat.{u, u})
    (v w : (N.obj D).obj (op ⦋0⦌)) :
    SimplexIndex (rightConeSimplices.{u} D v w) ⥤ SSet.{u} :=
  CostructuredArrow.proj uliftYoneda.{u} (rightConeSimplices.{u} D v w) ⋙
    QFunctor.{u}

/-- A right-cone simplex evaluates by the original counit, at the fixed endpoints. -/
def rightConeEvaluation (D : SimplicialCat.{u, u})
    (v w : (N.obj D).obj (op ⦋0⦌)) (n : ℕ)
    (σ : (rightConeSimplices.{u} D v w).obj (op ⦋n⦌)) :
    Q.{u} n ⟶ D.enriched.Hom
      (OrdinaryRigidification.NerveVertices.vertexEquiv D v)
      (OrdinaryRigidification.NerveVertices.vertexEquiv D w) :=
  evaluation.{u} D n σ.1 ≫
    targetHomTransport
      (congrArg (OrdinaryRigidification.NerveVertices.vertexEquiv D) σ.2.1)
      (congrArg (OrdinaryRigidification.NerveVertices.vertexEquiv D) σ.2.2)

end

end DaggerOriginalCounitBNextConeEvaluationIndex
