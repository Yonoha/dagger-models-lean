import NativeHorizontalPiRestriction
import NativeHorizontalMappingPushout

/-! Original compatible pi families glue uniquely over every actual horizontal pushout. -/
set_option autoImplicit false
open CategoryTheory Limits Simplicial Opposite
open DaggerNativeBisimplicialHorizontalMapping DaggerNativeHorizontalPiCompatibility
open DaggerNativeHorizontalPiSections DaggerNativeHorizontalPiRestriction
universe u
namespace DaggerNativeHorizontalPiGluing
noncomputable section

variable {K₀ K₁ K₂ K₃ : SSet.{u}} {i : K₀ ⟶ K₁} {j : K₀ ⟶ K₂}
  {a : K₁ ⟶ K₃} {b : K₂ ⟶ K₃}

def GluableFamilies (i : K₀ ⟶ K₁) (j : K₀ ⟶ K₂) (a : K₁ ⟶ K₃) (b : K₂ ⟶ K₃)
    (X : BiSSet.{u}) (t : ℕ) (v : (horizontalMapping K₃ X) _⦋0⦌) :=
  {z : CompatiblePiFamily K₁ X t (restrictedVertex a X v) ×
      CompatiblePiFamily K₂ X t (restrictedVertex b X v) //
    i ≫ familyMap K₁ X t (restrictedVertex a X v) z.1 =
      j ≫ familyMap K₂ X t (restrictedVertex b X v) z.2}

def gluingComparison (h : IsPushout i j a b) (X : BiSSet.{u}) (t : ℕ)
    (v : (horizontalMapping K₃ X) _⦋0⦌) :
    CompatiblePiFamily K₃ X t v → GluableFamilies i j a b X t v := fun s ↦
  ⟨⟨restrictFamily a X t v s, restrictFamily b X t v s⟩, by
    rw [familyMap_restrict, familyMap_restrict, ← Category.assoc, ← Category.assoc, h.w]⟩

theorem gluingComparison_injective (h : IsPushout i j a b) (X : BiSSet.{u}) (t : ℕ)
    (v : (horizontalMapping K₃ X) _⦋0⦌) :
    Function.Injective (gluingComparison h X t v) := by
  intro s r he
  apply familyMap_injective K₃ X t v
  apply h.hom_ext
  · exact congrArg (familyMap K₁ X t (restrictedVertex a X v))
      (congrArg (fun z ↦ z.val.1) he)
  · exact congrArg (familyMap K₂ X t (restrictedVertex b X v))
      (congrArg (fun z ↦ z.val.2) he)

theorem gluingComparison_surjective (h : IsPushout i j a b) (X : BiSSet.{u}) (t : ℕ)
    (v : (horizontalMapping K₃ X) _⦋0⦌) :
    Function.Surjective (gluingComparison h X t v) := by
  intro z
  obtain ⟨f, hf₁, hf₂⟩ := h.exists_desc
    (familyMap K₁ X t (restrictedVertex a X v) z.val.1)
    (familyMap K₂ X t (restrictedVertex b X v) z.val.2) z.property
  have hf : f ≫ rowProjection X t = vertexMap K₃ X v := by
    apply h.hom_ext
    · rw [← Category.assoc, hf₁]
      rfl
    · rw [← Category.assoc, hf₂]
      rfl
  let s := sectionFamily K₃ X t v ⟨f, hf⟩
  have hs : familyMap K₃ X t v s = f := by
    exact congrArg Subtype.val ((familySectionEquiv K₃ X t v).apply_symm_apply ⟨f, hf⟩)
  refine ⟨s, Subtype.ext (Prod.ext ?_ ?_)⟩
  · apply familyMap_injective K₁ X t (restrictedVertex a X v)
    change familyMap K₁ X t (restrictedVertex a X v) (restrictFamily a X t v s) = _
    rw [familyMap_restrict, hs]
    exact hf₁
  · apply familyMap_injective K₂ X t (restrictedVertex b X v)
    change familyMap K₂ X t (restrictedVertex b X v) (restrictFamily b X t v s) = _
    rw [familyMap_restrict, hs]
    exact hf₂

theorem gluingComparison_bijective (h : IsPushout i j a b) (X : BiSSet.{u}) (t : ℕ)
    (v : (horizontalMapping K₃ X) _⦋0⦌) :
    Function.Bijective (gluingComparison h X t v) :=
  ⟨gluingComparison_injective h X t v, gluingComparison_surjective h X t v⟩

end
end DaggerNativeHorizontalPiGluing
