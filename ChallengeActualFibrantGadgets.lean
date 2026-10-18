import ActualFibrantGadgetData
import Mathlib.AlgebraicTopology.Quasicategory.Basic
import Mathlib.CategoryTheory.Comma.Over.Basic
import TopCatModelCategory.ModelCategorySSet

/-! The problem keeps the chosen C, N, replacement, unit, and all full extended maps. -/
set_option autoImplicit false
open CategoryTheory HomotopicalAlgebra Opposite DaggerModels OrdinaryRigidification
open OriginalOrdinaryLocalKanReplacement DaggerActualFibrantGadgetData
open scoped Simplicial SSet.modelCategoryQuillen
universe u
namespace DaggerActualFibrantGadgetsChallenge

def statement : Prop :=
  (∀ X : SSet.{u}, SSet.Quasicategory (gadget.obj X) ∧
    Function.Bijective ((DaggerActualFibrantGadgetData.unit.app X).app (op ⦋0⦌)) ∧
    ∀ a b : (rigidification.obj X).Obj,
      SSet.anodyneExtensions
        ((OriginalOrdinaryLocalKanReplacement.unit.app (rigidification.obj X)).map a b)) ∧
  (∀ D : SimplicialCat.{u, u},
    (∀ x y : D.Obj, SSet.KanComplex (x ⟶[SSet.{u}] y)) →
    ∃ r : replacement.obj D ⟶ D,
      OriginalOrdinaryLocalKanReplacement.unit.app D ≫ r = 𝟙 D ∧
      (∀ (X : SSet.{u}) (σ : X ⟶ coherentNerve.obj D),
        DaggerActualFibrantGadgetData.unit.app X ≫ extension D r σ = σ) ∧
      (∀ (X Y : SSet.{u}) (f : X ⟶ Y) (σ : Y ⟶ coherentNerve.obj D),
        gadget.map f ≫ extension D r σ = extension D r (f ≫ σ)) ∧
      ∃ G : Over (coherentNerve.obj D) ⥤ Over (coherentNerve.obj D),
        ∃ α : 𝟭 (Over (coherentNerve.obj D)) ⟶ G,
          (∀ X, G.obj X = Over.mk (extension D r X.hom)) ∧
          (∀ (X Y : Over (coherentNerve.obj D)) (f : X ⟶ Y),
            HEq ((G.map f).left) (gadget.map f.left)) ∧
          (∀ X, HEq ((α.app X).left) (DaggerActualFibrantGadgetData.unit.app X.left))) ∧
  ∀ (A B : SimplicialCat.{u, u}) (p : A ⟶ B),
    Function.Surjective p.obj →
    (∀ a b : A.Obj, trivialFibrations SSet.{u} (p.map a b)) →
    trivialFibrations SSet.{u} (coherentNerve.map p) ∧
    (∀ a b : (rigidification.obj (coherentNerve.obj A)).Obj,
      SSet.KanComplex.W (TopCat.toSSet.map (SSet.toTop.map
        ((rigidification.map (coherentNerve.map p)).map a b)))) ∧
    Function.Surjective (rigidification.map (coherentNerve.map p)).obj

end DaggerActualFibrantGadgetsChallenge
