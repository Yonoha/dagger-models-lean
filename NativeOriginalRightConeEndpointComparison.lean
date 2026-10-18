import ActualRightConeFunctorialComparisons
import OriginalOrdinaryMovingHomDiagramReconciled

/-! The OLD right-cone/Q-singular ISO retains BOTH explicitly prescribed native vertices. -/
set_option autoImplicit false
open CategoryTheory Opposite Simplicial DaggerModels OrdinaryRigidification
open DaggerOriginalCounitBNextConeEvaluationIndex
open DaggerOriginalCounitBNextConeRealizationFactorization
open DaggerOriginalCounitRightConeQRealizationAdjunction
open DaggerActualRightConeFunctorialComparisons
open DaggerModels.OriginalOrdinaryMovingHomColimits
universe u
namespace DaggerNativeOriginalRightConeEndpointComparison
noncomputable section

variable {C D : SimplicialCat.{u, u}} (F : C ⟶ D)
variable (x y : (coherentNerve.obj C) _⦋0⦌) (a b : (coherentNerve.obj D) _⦋0⦌)
variable (hx : (coherentNerve.map F).app (op ⦋0⦌) x = a)
variable (hy : (coherentNerve.map F).app (op ⦋0⦌) y = b)

def postcompTo : rightConeSimplices C x y ⟶ rightConeSimplices D a b := by
  subst a
  subst b
  exact postcomp F x y

theorem postcompTo_raw (n : SimplexCategoryᵒᵖ) (v : (rightConeSimplices C x y).obj n) :
    ((postcompTo F x y a b hx hy).app n v).val = v.val ≫ coherentNerve.map F := by
  subst a
  subst b
  rfl

def homMapTo :
    (NerveVertices.vertexEquiv C x ⟶[SSet.{u}] NerveVertices.vertexEquiv C y) ⟶
      (NerveVertices.vertexEquiv D a ⟶[SSet.{u}] NerveVertices.vertexEquiv D b) := by
  subst a
  subst b
  exact DaggerActualRightConeFunctorialComparisons.homMap F x y

theorem homMapTo_formula :
    homMapTo F x y a b hx hy =
      castMap F (NerveVertices.vertexEquiv C x) (NerveVertices.vertexEquiv C y)
        (NerveVertices.vertexEquiv D a) (NerveVertices.vertexEquiv D b)
        ((NerveVertices.vertexEquiv_naturality F x).trans
          (congrArg (NerveVertices.vertexEquiv D) hx))
        ((NerveVertices.vertexEquiv_naturality F y).trans
          (congrArg (NerveVertices.vertexEquiv D) hy)) := by
  subst a
  subst b
  simp only [homMapTo, DaggerActualRightConeFunctorialComparisons.homMap, castMap,
    OriginalOrdinaryEndpointTransport.transport, eqToHom_refl, Category.comp_id]

theorem comparison_naturalityTo :
    postcompTo F x y a b hx hy ≫ coneSingularComparison D a b =
      coneSingularComparison C x y ≫ singular.map (homMapTo F x y a b hx hy) := by
  subst a
  subst b
  exact DaggerActualRightConeFunctorialComparisons.comparison_naturality F x y

end
end DaggerNativeOriginalRightConeEndpointComparison
