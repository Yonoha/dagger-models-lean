import OriginalCounitBNextConeRealizationFactorizationReconciled
import SSetGluing
import Mathlib.AlgebraicTopology.SimplicialSet.KanComplex

/-! Original right-cone maps, with all simplices and exact original Hom endpoints. -/

set_option autoImplicit false
open CategoryTheory Limits Opposite Simplicial EnrichedCategory HomotopicalAlgebra
open DaggerModels DaggerModels.OrdinaryRigidification
open DaggerOriginalCounitRightCone
open DaggerOriginalCounitBNextConeEvaluationIndex
open DaggerOriginalCounitBNextConeRealizationFactorization
open DaggerOriginalCounitRightConeQRealizationAdjunction
open DaggerModels.OriginalOrdinaryMovingHomColimits DaggerSSetGluing
universe u

namespace DaggerActualRightConeNaturalityChallenge
noncomputable section
variable {D E : SimplicialCat.{u, u}} (F : D ⟶ E)
variable (v w : (coherentNerve.obj D).obj (op ⦋0⦌))

def vertexMap (v : (coherentNerve.obj D).obj (op ⦋0⦌)) :
    (coherentNerve.obj E).obj (op ⦋0⦌) := (coherentNerve.map F).app (op ⦋0⦌) v

def postcomp : rightConeSimplices D v w ⟶
    rightConeSimplices E (vertexMap F v) (vertexMap F w) where
  app q σ := ⟨σ.1 ≫ coherentNerve.map F, by
    constructor
    · change (coherentNerve.map F).app (op ⦋0⦌) (σ.1.app _ (alpha q.unop.len)) = _
      rw [σ.2.1]
      rfl
    · change (coherentNerve.map F).app (op ⦋0⦌) (σ.1.app _ (omega q.unop.len)) = _
      rw [σ.2.2]
      rfl⟩
  naturality q r f := by
    funext σ
    apply Subtype.ext
    exact Category.assoc _ _ _

def rigidificationHomMap :
    ((rigidification.obj (coherentNerve.obj D)).enriched.Hom
      (RigidificationVertices.vertexEquiv _ v) (RigidificationVertices.vertexEquiv _ w)) ⟶
    ((rigidification.obj (coherentNerve.obj E)).enriched.Hom
      (RigidificationVertices.vertexEquiv _ (vertexMap F v))
      (RigidificationVertices.vertexEquiv _ (vertexMap F w))) :=
  castMap (rigidification.map (coherentNerve.map F))
    (RigidificationVertices.vertexEquiv _ v) (RigidificationVertices.vertexEquiv _ w)
    (RigidificationVertices.vertexEquiv _ (vertexMap F v))
    (RigidificationVertices.vertexEquiv _ (vertexMap F w))
    (RigidificationVertices.vertexEquiv_naturality (coherentNerve.map F) v)
    (RigidificationVertices.vertexEquiv_naturality (coherentNerve.map F) w)

def statement : Prop :=
  ∀ D : SimplicialCat.{u, u},
    (∀ x y : D.Obj, SSet.KanComplex (D.enriched.Hom x y)) →
    (∀ v w : (coherentNerve.obj D).obj (op ⦋0⦌), (rightConeSimplices D v w).KanComplex) ∧
    ∀ (E : SimplicialCat.{u, u}) (F : D ⟶ E),
      (∀ x y : E.Obj, SSet.KanComplex (E.enriched.Hom x y)) →
      (∀ v w : (coherentNerve.obj D).obj (op ⦋0⦌),
        GW (postcomp F v w) ↔
          GW (F.map (NerveVertices.vertexEquiv D v) (NerveVertices.vertexEquiv D w))) ∧
      (∀ v w : (coherentNerve.obj D).obj (op ⦋0⦌),
        realization.map (postcomp F v w) ≫
          coneRigidificationMap E (vertexMap F v) (vertexMap F w) =
        coneRigidificationMap D v w ≫ rigidificationHomMap F v w) ∧
      ((∀ v w : (coherentNerve.obj D).obj (op ⦋0⦌), GW (postcomp F v w)) ↔
        ∀ x y : D.Obj, GW (F.map x y)) ∧
      ∀ (v w : (coherentNerve.obj D).obj (op ⦋0⦌)) (n : ℕ)
        (σ : (rightConeSimplices D v w).obj (op ⦋n⦌)),
        rightConeEvaluation E (vertexMap F v) (vertexMap F w) n ((postcomp F v w).app _ σ) =
          rightConeEvaluation D v w n σ ≫
            F.map (NerveVertices.vertexEquiv D v) (NerveVertices.vertexEquiv D w)

end
end DaggerActualRightConeNaturalityChallenge
