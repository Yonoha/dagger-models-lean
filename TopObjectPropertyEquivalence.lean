import Mathlib.CategoryTheory.Presentable.Adjunction

/-! The full category on all objects reuses the original category without extra hypotheses. -/
set_option autoImplicit false
open CategoryTheory
universe u v w
namespace DaggerTopObjectPropertyEquivalence
noncomputable section
variable (C : Type w) [Category.{v} C]

def equivalence : C ≌ (⊤ : ObjectProperty C).FullSubcategory where
  functor :=
    { obj X := ⟨X, trivial⟩
      map f := ObjectProperty.homMk f }
  inverse := (⊤ : ObjectProperty C).ι
  unitIso := Iso.refl _
  counitIso := Iso.refl _

theorem accessible (κ : Cardinal.{u}) [Fact κ.IsRegular]
    [IsCardinalAccessibleCategory.{u} C κ] :
    IsCardinalAccessibleCategory.{u} (⊤ : ObjectProperty C).FullSubcategory κ :=
  (equivalence C).isCardinalAccessibleCategory κ

theorem inclusion_accessible (κ : Cardinal.{u}) [Fact κ.IsRegular] :
    (⊤ : ObjectProperty C).ι.IsCardinalAccessible κ := by
  change (equivalence C).inverse.IsCardinalAccessible κ
  infer_instance

end
end DaggerTopObjectPropertyEquivalence
