import OriginalFlagGateRowGeometric
import OriginalFlagOuterDegree

set_option autoImplicit false
open CategoryTheory Limits Opposite Simplicial
open DaggerChosenRigidificationNecklace
open DaggerOriginalFlagFlankification

universe u

namespace DaggerOriginalProductGadget

noncomputable section

variable {X : SSet.{u}} (a b : X.obj (op ⦋0⦌)) (A : Set (X.obj (op ⦋0⦌)))
  (R₀ : X.obj (op ⦋0⦌) → X.obj (op ⦋0⦌) → Prop)

/-- The original simplex operator restricted to each actual gate subcomplex. -/
def gateDegreeTransition {q r : SimplexCategoryᵒᵖ} (α : q ⟶ r) :
    flagGateDegreeDiagram a b A R₀ q ⟶ flagGateDegreeDiagram a b A R₀ r where
  app S := (flagGateDiagram a b A R₀).obj S |>.map α
  naturality _ _ _ := by
    funext x
    rfl

/-- The induced operator on the actual categories of elements, retaining all index arrows. -/
def gateDegreeMap {q r : SimplexCategoryᵒᵖ} (α : q ⟶ r) :
    (flagGateDegreeDiagram a b A R₀ q).Elements ⥤
      (flagGateDegreeDiagram a b A R₀ r).Elements :=
  NatTrans.mapElements (gateDegreeTransition a b A R₀ α)

theorem gateDegreeMap_obj_index {q r : SimplexCategoryᵒᵖ} (α : q ⟶ r)
    (p : (flagGateDegreeDiagram a b A R₀ q).Elements) :
    ((gateDegreeMap a b A R₀ α).obj p).1 = p.1 := rfl

theorem gateDegreeMap_obj_value {q r : SimplexCategoryᵒᵖ} (α : q ⟶ r)
    (p : (flagGateDegreeDiagram a b A R₀ q).Elements) :
    ((gateDegreeMap a b A R₀ α).obj p).2.val = (flagHom X a b).map α p.2.val := rfl

theorem gateDegreeMap_id (q : SimplexCategoryᵒᵖ) :
    gateDegreeMap a b A R₀ (𝟙 q) = 𝟭 _ := by
  refine CategoryTheory.Functor.ext (fun p ↦ ?_)
  exact Sigma.ext rfl (heq_of_eq (Subtype.ext
    (FunctorToTypes.map_id_apply (flagHom X a b) p.2.val)))

theorem gateDegreeMap_comp {q r s : SimplexCategoryᵒᵖ} (α : q ⟶ r) (β : r ⟶ s) :
    gateDegreeMap a b A R₀ (α ≫ β) =
      gateDegreeMap a b A R₀ α ⋙ gateDegreeMap a b A R₀ β := by
  refine CategoryTheory.Functor.ext (fun p ↦ ?_)
  exact Sigma.ext rfl (heq_of_eq (Subtype.ext
    (FunctorToTypes.map_comp_apply (flagHom X a b) α β p.2.val)))

/-- The entire bisimplicial nerve of the actual gate degree diagram. -/
def gateOuterNerve : SimplexCategoryᵒᵖ ⥤ SSet.{u} where
  obj q := nerve (flagGateDegreeDiagram a b A R₀ q).Elements
  map α := nerveMap (gateDegreeMap a b A R₀ α)
  map_id q := by rw [gateDegreeMap_id]; rfl
  map_comp α β := by rw [gateDegreeMap_comp]; rfl

/-- Each row is the same gate augmentation followed by the existing discrete-nerve isomorphism. -/
def gateOuterAugmentation (q : SimplexCategoryᵒᵖ) :
    (gateOuterNerve a b A R₀).obj q ⟶ (outerConstant X a b).obj q :=
  nerveMap (flagGateRowAugmentation a b A R₀ q) ≫
    (nerveDiscreteIso ((flagHom X a b).obj q)).hom

theorem gateOuterAugmentation_app (q k : SimplexCategoryᵒᵖ)
    (gamma : ((gateOuterNerve a b A R₀).obj q).obj k) :
    (gateOuterAugmentation a b A R₀ q).app k gamma = (gamma.obj 0).2.val := rfl

theorem gateOuterAugmentation_naturality {q r : SimplexCategoryᵒᵖ} (α : q ⟶ r) :
    (gateOuterNerve a b A R₀).map α ≫ gateOuterAugmentation a b A R₀ r =
      gateOuterAugmentation a b A R₀ q ≫ (outerConstant X a b).map α := by
  ext k gamma
  rfl

/-- The full augmentation includes every outer simplex operator and every inner nerve operator. -/
def gateOuterEta : gateOuterNerve a b A R₀ ⟶ outerConstant X a b where
  app q := gateOuterAugmentation a b A R₀ q
  naturality _ _ α := gateOuterAugmentation_naturality a b A R₀ α

/-- The actual diagonal augmentation has the original flag Hom as target. -/
def gateDiagonalAugmentation :
    DaggerBisimplicialDiagonal.diag (gateOuterNerve a b A R₀) ⟶ flagHom X a b :=
  DaggerBisimplicialDiagonal.diagMap (gateOuterEta a b A R₀) ≫
    eqToHom (diagonal_outerConstant X a b)

theorem gateDiagonalAugmentation_app (q : SimplexCategoryᵒᵖ)
    (gamma : (DaggerBisimplicialDiagonal.diag (gateOuterNerve a b A R₀)).obj q) :
    (gateDiagonalAugmentation a b A R₀).app q gamma = (gamma.obj 0).2.val := rfl

end

end DaggerOriginalProductGadget
