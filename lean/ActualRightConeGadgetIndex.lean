import ActualNecklaceConeGadgets
import OriginalCounitBNextConeRealizationFactorizationReconciled

/-! Insert the literal right-cone simplex category into the common gadget category.
Every simplex operator is sent to the original `coneMap`. No cofinality is assumed. -/

set_option autoImplicit false
open CategoryTheory Opposite Simplicial
open DaggerModels DaggerOriginalCounitRightCone DaggerOriginalCounitRightConeFunctor
open DaggerOriginalCounitBNextConeEvaluationIndex
open DaggerOriginalCounitRightConeQFunctor
open DaggerOriginalCounitRightConeQRealizationAdjunction
universe u

namespace DaggerActualRightConeGadgetIndex
noncomputable section
open DaggerActualNecklaceConeGadgets

def coneOperator {m n : SimplexCategory} (f : m ⟶ n) :
    (Sum.inr m.len : Code) ⟶ Sum.inr n.len :=
  ⟨coneMap.{u} f, alpha_naturality f, omega_naturality f⟩

def coneEmbedding : SimplexCategory ⥤ Code where
  obj n := Sum.inr n.len
  map := coneOperator.{u}
  map_id n := Hom.ext (coneFunctor.{u}.map_id n)
  map_comp f g := Hom.ext (coneFunctor.{u}.map_comp f g)

def indexObj (D : SimplicialCat.{u, u})
    (v w : (OrdinaryRigidification.coherentNerve.obj D).obj (op ⦋0⦌))
    (σ : SimplexIndex (rightConeSimplices D v w)) :
    Over (OrdinaryRigidification.coherentNerve.obj D) v w :=
  ⟨Sum.inr σ.left.len, (uliftYonedaEquiv σ.hom).val,
    (uliftYonedaEquiv σ.hom).property.1, (uliftYonedaEquiv σ.hom).property.2⟩

def index (D : SimplicialCat.{u, u})
    (v w : (OrdinaryRigidification.coherentNerve.obj D).obj (op ⦋0⦌)) :
    SimplexIndex (rightConeSimplices D v w) ⥤
      Over (OrdinaryRigidification.coherentNerve.obj D) v w where
  obj := indexObj D v w
  map {σ τ} f := ⟨coneOperator f.left, by
    have hs : (rightConeSimplices D v w).map f.left.op
        (uliftYonedaEquiv τ.hom) = uliftYonedaEquiv σ.hom := by
      simpa only [Quiver.Hom.unop_op, CostructuredArrow.w f] using
        (uliftYonedaEquiv_naturality (F := rightConeSimplices D v w) τ.hom f.left.op)
    exact congrArg Subtype.val hs⟩
  map_id σ := by apply Over.Hom.ext; exact (coneEmbedding.{u}).map_id σ.left
  map_comp f g := by apply Over.Hom.ext; exact (coneEmbedding.{u}).map_comp f.left g.left

/-- The gadget stores the entire original cone simplex, not merely endpoint or degree data. -/
theorem index_obj_map (D : SimplicialCat.{u, u})
    (v w : (OrdinaryRigidification.coherentNerve.obj D).obj (op ⦋0⦌))
    (σ : SimplexIndex (rightConeSimplices D v w)) :
    ((index D v w).obj σ).map = (uliftYonedaEquiv σ.hom).val := rfl

/-- Every original operator survives unchanged in the common category. -/
theorem index_map_original (D : SimplicialCat.{u, u})
    (v w : (OrdinaryRigidification.coherentNerve.obj D).obj (op ⦋0⦌))
    {σ τ : SimplexIndex (rightConeSimplices D v w)} (f : σ ⟶ τ) :
    ((index D v w).map f).hom.map = coneMap.{u} f.left := rfl

end
end DaggerActualRightConeGadgetIndex
