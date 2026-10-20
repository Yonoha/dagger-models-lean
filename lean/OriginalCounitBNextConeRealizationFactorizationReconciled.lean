import OriginalCounitRightConeQRealizationAdjunctionReconciled
import OriginalCounitBNextConeCounitFactorizationReconciled

/-!
# Realized right-cone evaluation and the original counit

Descend the two existing literal right-cone cocones through the actual Q
realization, keeping the original Hom targets and both vertex transports.
Their descended maps factor through the original counit. Transposition gives
an actual simplicial comparison with Q-singular of the same target Hom.
No weak-equivalence assertion is assumed or made in this module.
-/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite Simplicial EnrichedCategory
open DaggerModels
open DaggerOriginalCounitRightConeQFunctor
open DaggerOriginalCounitBNextConeEvaluationIndex
open DaggerOriginalCounitBNextConeEvaluationNaturality
open DaggerOriginalCounitBNextConeCounitFactorization
open DaggerOriginalCounitRightConeQRealizationAdjunction

universe u

namespace DaggerOriginalCounitBNextConeRealizationFactorization

noncomputable section

private abbrev C := OrdinaryRigidification.rigidification.{u}
private abbrev N := OrdinaryRigidification.coherentNerve.{u}
private abbrev RV := OrdinaryRigidification.RigidificationVertices.vertexEquiv.{u}

/-- The descended evaluation lands in the exact original Hom of D. -/
def coneEvaluationMap (D : SimplicialCat.{u, u})
    (v w : (N.obj D).obj (op ⦋0⦌)) :
    realization.obj (rightConeSimplices D v w) ⟶ D.enriched.Hom
      (OrdinaryRigidification.NerveVertices.vertexEquiv D v)
      (OrdinaryRigidification.NerveVertices.vertexEquiv D w) :=
  (simplexCoconeIsColimit (rightConeSimplices D v w)).desc
    (rightConeEvaluationCocone D v w)

/-- The descended rigidification leg lands in the original C(N(D)) Hom with RV labels. -/
def coneRigidificationMap (D : SimplicialCat.{u, u})
    (v w : (N.obj D).obj (op ⦋0⦌)) :
    realization.obj (rightConeSimplices D v w) ⟶
      (C.obj (N.obj D)).enriched.Hom (RV (N.obj D) v) (RV (N.obj D) w) :=
  (simplexCoconeIsColimit (rightConeSimplices D v w)).desc
    (rightConeRigidificationCocone D v w)

/-- Every literal simplex leg of realization has the original counit evaluation. -/
theorem coneEvaluationMap_leg (D : SimplicialCat.{u, u})
    (v w : (N.obj D).obj (op ⦋0⦌)) (σ : SimplexIndex (rightConeSimplices D v w)) :
    realizationUnit.app σ.left ≫ realization.map σ.hom ≫ coneEvaluationMap D v w =
      rightConeEvaluation D v w σ.left.len (uliftYonedaEquiv σ.hom) :=
  (simplexCoconeIsColimit (rightConeSimplices D v w)).fac
    (rightConeEvaluationCocone D v w) σ

/-- The rigidification descent likewise retains the exact original cone Hom leg. -/
theorem coneRigidificationMap_leg (D : SimplicialCat.{u, u})
    (v w : (N.obj D).obj (op ⦋0⦌)) (σ : SimplexIndex (rightConeSimplices D v w)) :
    realizationUnit.app σ.left ≫ realization.map σ.hom ≫ coneRigidificationMap D v w =
      rightConeRigidificationLeg D v w σ.left.len (uliftYonedaEquiv σ.hom) :=
  (simplexCoconeIsColimit (rightConeSimplices D v w)).fac
    (rightConeRigidificationCocone D v w) σ

/-- The realized evaluation factors through the precise original transported counit Hom. -/
theorem coneEvaluationMap_factor (D : SimplicialCat.{u, u})
    (v w : (N.obj D).obj (op ⦋0⦌)) :
    coneRigidificationMap D v w ≫ counitHom D v w = coneEvaluationMap D v w := by
  apply (simplexCoconeIsColimit (rightConeSimplices D v w)).hom_ext
  intro σ
  change (realizationUnit.app σ.left ≫ realization.map σ.hom) ≫
      (coneRigidificationMap D v w ≫ counitHom D v w) =
    (realizationUnit.app σ.left ≫ realization.map σ.hom) ≫ coneEvaluationMap D v w
  rw [← Category.assoc,
    Category.assoc (realizationUnit.app σ.left) (realization.map σ.hom)
      (coneRigidificationMap D v w), coneRigidificationMap_leg,
    rightConeEvaluation_factor,
    Category.assoc (realizationUnit.app σ.left) (realization.map σ.hom)
      (coneEvaluationMap D v w), coneEvaluationMap_leg]

/-- Transpose the exact descended evaluation under the original-Q adjunction. -/
def coneSingularComparison (D : SimplicialCat.{u, u})
    (v w : (N.obj D).obj (op ⦋0⦌)) :
    rightConeSimplices D v w ⟶ singular.obj
      (D.enriched.Hom
        (OrdinaryRigidification.NerveVertices.vertexEquiv D v)
        (OrdinaryRigidification.NerveVertices.vertexEquiv D w)) :=
  realizationSingularAdjunction.homEquiv _ _ (coneEvaluationMap D v w)

/-- In every degree the singular comparison is precisely the original cone evaluation. -/
theorem coneSingularComparison_app (D : SimplicialCat.{u, u})
    (v w : (N.obj D).obj (op ⦋0⦌)) (q : SimplexCategoryᵒᵖ)
    (σ : (rightConeSimplices D v w).obj q) :
    ((coneSingularComparison D v w).app q σ).down =
      rightConeEvaluation D v w q.unop.len σ := by
  change (((Presheaf.uliftYonedaAdjunction.{u}
    (uliftYoneda.{u}.leftKanExtension QFunctor.{u})
    (uliftYoneda.{u}.leftKanExtensionUnit QFunctor.{u})).homEquiv
      _ _ (coneEvaluationMap D v w)).app q σ).down =
    rightConeEvaluation D v w q.unop.len σ
  rw [Presheaf.uliftYonedaAdjunction_homEquiv_app]
  change realizationUnit.app q.unop ≫ realization.map (uliftYonedaEquiv.symm σ) ≫
    coneEvaluationMap D v w = rightConeEvaluation D v w q.unop.len σ
  have h := coneEvaluationMap_leg D v w (CostructuredArrow.mk (uliftYonedaEquiv.symm σ))
  change realizationUnit.app q.unop ≫ realization.map (uliftYonedaEquiv.symm σ) ≫
    coneEvaluationMap D v w = rightConeEvaluation D v w q.unop.len
      (uliftYonedaEquiv (uliftYonedaEquiv.symm σ)) at h
  simpa only [Equiv.apply_symm_apply] using h

end

end DaggerOriginalCounitBNextConeRealizationFactorization
