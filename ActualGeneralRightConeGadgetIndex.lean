import ActualRightConeGadgetIndex
import ActualGeneralRightConeMapping

/-! Reuse ORIGINAL cone operators to index literal right mappings into EVERY simplicial X. -/
set_option autoImplicit false
open CategoryTheory Opposite Simplicial
open DaggerActualNecklaceConeGadgets DaggerActualGeneralRightConeMapping
open DaggerOriginalCounitRightConeQRealizationAdjunction
universe u
namespace DaggerActualGeneralRightConeGadgetIndex
noncomputable section

variable (X : SSet.{u}) (a b : X.obj (op ⦋0⦌))

def indexObj (σ : SimplexIndex (rightMapping X a b)) : Over X a b :=
  ⟨Sum.inr σ.left.len, (uliftYonedaEquiv σ.hom).val,
    (uliftYonedaEquiv σ.hom).property.1, (uliftYonedaEquiv σ.hom).property.2⟩

def index : SimplexIndex (rightMapping X a b) ⥤ Over X a b where
  obj := indexObj X a b
  map {σ τ} f := ⟨DaggerActualRightConeGadgetIndex.coneOperator f.left, by
    have hs : (rightMapping X a b).map f.left.op
        (uliftYonedaEquiv τ.hom) = uliftYonedaEquiv σ.hom := by
      simpa only [Quiver.Hom.unop_op, CostructuredArrow.w f] using
        (uliftYonedaEquiv_naturality (F := rightMapping X a b) τ.hom f.left.op)
    exact congrArg Subtype.val hs⟩
  map_id σ := by
    apply Over.Hom.ext
    exact DaggerActualRightConeGadgetIndex.coneEmbedding.map_id σ.left
  map_comp f g := by
    apply Over.Hom.ext
    exact DaggerActualRightConeGadgetIndex.coneEmbedding.map_comp f.left g.left

theorem index_obj_map (σ : SimplexIndex (rightMapping X a b)) :
    ((index X a b).obj σ).map = (uliftYonedaEquiv σ.hom).val := rfl

end
end DaggerActualGeneralRightConeGadgetIndex
