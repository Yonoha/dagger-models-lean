import Mathlib.AlgebraicTopology.SimplicialSet.Nerve
import Mathlib.CategoryTheory.Category.ULift
import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic

/-! Independent Mathlib-only statement fixing the complete original column cells. -/
set_option autoImplicit false
open CategoryTheory Opposite Simplicial
universe u
namespace DaggerNativeSimplexColumnBijectionChallenge
noncomputable section

abbrev Index (X : SSet.{u}) := CostructuredArrow uliftYoneda.{u, 0, 0} X
abbrev LiftedIndex (X : SSet.{u}) := ULiftHom.{u} (Index X)

def simplex (X : SSet.{u}) (k : SimplexCategoryᵒᵖ) (x : X.obj k) : LiftedIndex X :=
  ULiftHom.up.{0, u, u}.obj (CostructuredArrow.mk
    (uliftYonedaEquiv.symm x : uliftYoneda.{u, 0, 0}.obj k.unop ⟶ X))

abbrev Source (X : SSet.{u}) (q k : SimplexCategoryᵒᵖ) :=
  Σ x : X.obj k, (nerve (StructuredArrow (simplex X k x) (𝟭 (LiftedIndex X)))).obj q

abbrev Target (X : SSet.{u}) (q k : SimplexCategoryᵒᵖ) :=
  Σ c : (nerve (LiftedIndex X)).obj q,
    (uliftYoneda.{u, 0, 0}.obj (ULiftHom.down.{0, u, u}.obj (c.obj 0)).left).obj k

/-- Project the full original chain and keep the full starting simplex operator. -/
def wholeChainMap (X : SSet.{u}) (q k : SimplexCategoryᵒᵖ) (z : Source X q k) : Target X q k :=
  ⟨z.2 ⋙ StructuredArrow.proj (simplex X k z.1) (𝟭 (LiftedIndex X)),
    ULift.up (z.2.obj 0).hom.down.left⟩

def statement : Prop :=
  ∀ (X : SSet.{u}) (q k : SimplexCategoryᵒᵖ), Function.Bijective (wholeChainMap X q k)

end
end DaggerNativeSimplexColumnBijectionChallenge
