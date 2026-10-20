import Mathlib.AlgebraicTopology.SimplicialSet.Nerve
import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic

/-! Independent Mathlib-only problem fixing every original object, arrow, and under-arrow. -/
set_option autoImplicit false
open CategoryTheory
universe u
namespace DaggerNativeStructuredArrowChainBijectionChallenge
noncomputable section

variable {C D : Type u} [Category.{u} C] [Category.{u} D] (F : C ⥤ D)

/-- Keep the whole projected chain and its entire first original arrow. -/
def wholeChainMap (d : D) (n : ℕ) (c : Fin (n + 1) ⥤ StructuredArrow d F) :
    Σ b : Fin (n + 1) ⥤ C, d ⟶ F.obj (b.obj 0) :=
  ⟨c ⋙ StructuredArrow.proj d F, (c.obj 0).hom⟩

def statement : Prop :=
  ∀ (C D : Type u) [Category.{u} C] [Category.{u} D]
    (F : C ⥤ D) (d : D) (n : ℕ), Function.Bijective (wholeChainMap F d n)

end
end DaggerNativeStructuredArrowChainBijectionChallenge
