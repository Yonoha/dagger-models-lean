import NativeHorizontalPiSections

/-! Restriction preserves every original row class and the canonical homotopy-group comparison. -/
set_option autoImplicit false
open CategoryTheory Simplicial Opposite SSet.KanComplex
open DaggerNativeBisimplicialHorizontalMapping DaggerNativeHorizontalPiCompatibility
open DaggerNativeHorizontalPiSections
universe u
namespace DaggerNativeHorizontalPiRestriction
noncomputable section

def restrictedVertex {K L : SSet.{u}} (i : K ⟶ L) (X : BiSSet.{u})
    (a : (horizontalMapping L X) _⦋0⦌) : (horizontalMapping K X) _⦋0⦌ :=
  (horizontalPre i X).app _ a

def restrictFamily {K L : SSet.{u}} (i : K ⟶ L) (X : BiSSet.{u}) (t : ℕ)
    (a : (horizontalMapping L X) _⦋0⦌) :
    CompatiblePiFamily L X t a → CompatiblePiFamily K X t (restrictedVertex i X a) :=
  fun s ↦ sectionFamily K X t (restrictedVertex i X a) ⟨i ≫ familyMap L X t a s, rfl⟩

theorem restrictFamily_value {K L : SSet.{u}} (i : K ⟶ L) (X : BiSSet.{u}) (t : ℕ)
    (a : (horizontalMapping L X) _⦋0⦌) (s : CompatiblePiFamily L X t a)
    (d : SimplexCategoryᵒᵖ) (x : K.obj d) :
    (restrictFamily i X t a s).val d x = s.val d (i.app d x) := rfl

theorem familyMap_restrict {K L : SSet.{u}} (i : K ⟶ L) (X : BiSSet.{u}) (t : ℕ)
    (a : (horizontalMapping L X) _⦋0⦌) (s : CompatiblePiFamily L X t a) :
    familyMap K X t (restrictedVertex i X a) (restrictFamily i X t a s) =
      i ≫ familyMap L X t a s := rfl

theorem familyMap_injective (K : SSet.{u}) (X : BiSSet.{u}) (t : ℕ)
    (a : (horizontalMapping K X) _⦋0⦌) : Function.Injective (familyMap K X t a) := by
  intro s r h
  apply (familySectionEquiv K X t a).injective
  exact Subtype.ext h

theorem restrictFamily_id (K : SSet.{u}) (X : BiSSet.{u}) (t : ℕ)
    (a : (horizontalMapping K X) _⦋0⦌) (s : CompatiblePiFamily K X t a) :
    familyMap K X t (restrictedVertex (𝟙 K) X a) (restrictFamily (𝟙 K) X t a s) =
      familyMap K X t a s := by
  rw [familyMap_restrict, Category.id_comp]

theorem restrictFamily_comp {K L M : SSet.{u}} (i : K ⟶ L) (j : L ⟶ M)
    (X : BiSSet.{u}) (t : ℕ) (a : (horizontalMapping M X) _⦋0⦌)
    (s : CompatiblePiFamily M X t a) :
    familyMap K X t (restrictedVertex (i ≫ j) X a) (restrictFamily (i ≫ j) X t a s) =
      i ≫ familyMap L X t (restrictedVertex j X a) (restrictFamily j X t a s) := by
  rw [familyMap_restrict, familyMap_restrict, Category.assoc]

theorem evaluation_restriction {K L : SSet.{u}} (i : K ⟶ L) (X : BiSSet.{u})
    (d : SimplexCategoryᵒᵖ) (x : K.obj d) :
    horizontalPre i X ≫ evaluation K X d x = evaluation L X d (i.app d x) := rfl

theorem piComparison_restrict {K L : SSet.{u}} (i : K ⟶ L) (X : BiSSet.{u}) (t : ℕ)
    (a : (horizontalMapping L X) _⦋0⦌) (s : π t (horizontalMapping L X) a) :
    piComparison K X t (restrictedVertex i X a)
        (mapπ (horizontalPre i X) t a (restrictedVertex i X a) rfl s) =
      restrictFamily i X t a (piComparison L X t a s) := by
  apply Subtype.ext
  funext d x
  exact mapπ_mapπ (horizontalPre i X) t a (restrictedVertex i X a) rfl
    (evaluation K X d x) _ rfl s

end
end DaggerNativeHorizontalPiRestriction
