import OriginalFlagRawPiZero
import BisimplicialDiagonalData

set_option autoImplicit false
open CategoryTheory Opposite Simplicial

universe u
namespace DaggerOriginalFlagFlankification
noncomputable section
open DaggerChosenRigidificationNecklace NecklaceCode

variable (X : SSet.{u}) (a b : X.obj (op ⦋0⦌))

/-- The same original category of elements at an arbitrary outer simplex. -/
abbrev outerDegree (q : SimplexCategoryᵒᵖ) :=
  (flagDegreeDiagram X a b q).Elements

/-- Restriction of the original flags, natural in the necklace. -/
def outerDegreeTransition {q r : SimplexCategoryᵒᵖ} (α : q ⟶ r) :
    flagDegreeDiagram X a b q ⟶ flagDegreeDiagram X a b r where
  app P := Flag.restrict α.unop.toOrderHom
  naturality P Q h := by
    funext F
    exact (Flag.restrict_map α.unop.toOrderHom h.hom F).symm

/-- The induced map acts on all arrows of the original category of elements. -/
def outerDegreeMap {q r : SimplexCategoryᵒᵖ} (α : q ⟶ r) :
    outerDegree X a b q ⥤ outerDegree X a b r :=
  NatTrans.mapElements (outerDegreeTransition X a b α)

theorem outerDegreeMap_obj {q r : SimplexCategoryᵒᵖ} (α : q ⟶ r)
    (p : outerDegree X a b q) :
    (outerDegreeMap X a b α).obj p =
      ⟨p.1, Flag.restrict α.unop.toOrderHom p.2⟩ := rfl

theorem outerDegreeMap_id (q : SimplexCategoryᵒᵖ) :
    outerDegreeMap X a b (𝟙 q) = 𝟭 (outerDegree X a b q) := by
  rfl

theorem outerDegreeMap_comp {q r s : SimplexCategoryᵒᵖ}
    (α : q ⟶ r) (β : r ⟶ s) :
    outerDegreeMap X a b (α ≫ β) =
      outerDegreeMap X a b α ⋙ outerDegreeMap X a b β := by
  rfl

/-- The original degree nerves, with their full outer simplicial action. -/
def outerNerve : SimplexCategoryᵒᵖ ⥤ SSet.{u} where
  obj q := nerve (outerDegree X a b q)
  map α := nerveMap (outerDegreeMap X a b α)
  map_id q := by
    rw [outerDegreeMap_id]
    rfl
  map_comp α β := by
    rw [outerDegreeMap_comp]
    rfl

/-- The literal constant inner simplicial set on each original flag quotient. -/
def outerConstant : SimplexCategoryᵒᵖ ⥤ SSet.{u} :=
  flagHom X a b ⋙ Functor.const SimplexCategoryᵒᵖ

def outerClassOf (q : SimplexCategoryᵒᵖ) (p : outerDegree X a b q) :
    (flagHom X a b).obj q :=
  Quot.mk (flagRelation X a b q) p

theorem outerClassOf_map (q : SimplexCategoryᵒᵖ)
    {p p' : outerDegree X a b q} (f : p ⟶ p') :
    outerClassOf X a b q p = outerClassOf X a b q p' :=
  Quot.sound ⟨f.val, f.property.symm⟩

def outerAugmentationFunctor (q : SimplexCategoryᵒᵖ) :
    outerDegree X a b q ⥤ Discrete ((flagHom X a b).obj q) where
  obj p := Discrete.mk (outerClassOf X a b q p)
  map f := Discrete.eqToHom (outerClassOf_map X a b q f)

/-- The original quotient augmentation in every outer degree. -/
def outerAugmentation (q : SimplexCategoryᵒᵖ) :
    (outerNerve X a b).obj q ⟶ (outerConstant X a b).obj q :=
  nerveMap (outerAugmentationFunctor X a b q) ≫
    (nerveDiscreteIso ((flagHom X a b).obj q)).hom

theorem outerAugmentation_app (q k : SimplexCategoryᵒᵖ)
    (gamma : ((outerNerve X a b).obj q).obj k) :
    (outerAugmentation X a b q).app k gamma =
      outerClassOf X a b q (gamma.obj 0) := rfl

theorem outerAugmentation_naturality {q r : SimplexCategoryᵒᵖ} (α : q ⟶ r) :
    (outerNerve X a b).map α ≫ outerAugmentation X a b r =
      outerAugmentation X a b q ≫ (outerConstant X a b).map α := by
  ext k gamma
  rfl

/-- The whole outer map whose rows are the original quotient augmentations. -/
def outerEta : outerNerve X a b ⟶ outerConstant X a b where
  app q := outerAugmentation X a b q
  naturality _ _ α := outerAugmentation_naturality X a b α

theorem outerEta_app_degree (n : ℕ) :
    (outerEta X a b).app (op ⦋n⦌) = constantAugmentation X a b n := rfl

theorem outerEta_row_geometric (n : ℕ) :
    SSet.KanComplex.W
      (TopCat.toSSet.map (SSet.toTop.map ((outerEta X a b).app (op ⦋n⦌)))) := by
  rw [outerEta_app_degree]
  exact constantAugmentation_geometric X a b n

theorem outerEta_row_rawPiZero_bijective (n : ℕ) :
    Function.Bijective (SSet.mapπ₀ ((outerEta X a b).app (op ⦋n⦌))) := by
  rw [outerEta_app_degree]
  exact constantAugmentation_mapPiZero_bijective X a b n

theorem diagonal_outerConstant :
    DaggerBisimplicialDiagonal.diag (outerConstant X a b) = flagHom X a b := rfl

/-- The diagonal of the whole outer map, with the original flag quotient target. -/
def diagonalAugmentation :
    DaggerBisimplicialDiagonal.diag (outerNerve X a b) ⟶ flagHom X a b :=
  DaggerBisimplicialDiagonal.diagMap (outerEta X a b) ≫
    eqToHom (diagonal_outerConstant X a b)

theorem diagonalAugmentation_app (n : ℕ) :
    (diagonalAugmentation X a b).app (op ⦋n⦌) =
      (constantAugmentation X a b n).app (op ⦋n⦌) := rfl

theorem diagonalAugmentation_representative (n : ℕ)
    (gamma : ((outerNerve X a b).obj (op ⦋n⦌)).obj (op ⦋n⦌)) :
    (diagonalAugmentation X a b).app (op ⦋n⦌) gamma =
      classOf X a b n (gamma.obj 0) := rfl

end
end DaggerOriginalFlagFlankification
