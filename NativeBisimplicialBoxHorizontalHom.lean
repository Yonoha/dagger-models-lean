import NativeBisimplicialBoxHom
import NativeBisimplicialHorizontalTranspose

/-! Reuse the original transpose to glue box maps in the horizontal parameter. -/
set_option autoImplicit false
open CategoryTheory Limits Simplicial Opposite
open DaggerNativeBisimplicialHorizontalMapping DaggerNativeBisimplicialBox
open DaggerNativeBisimplicialBoxHom DaggerNativeBisimplicialHorizontalTranspose
universe u
namespace DaggerNativeBisimplicialBoxHorizontalHom
noncomputable section

def horizontalBoxEquiv (K B : SSet.{u}) (X : BiSSet.{u}) :
    (box K B ⟶ X) ≃ (K ⟶ horizontalMapping B X.flip) :=
  (boxHomEquiv K B X).trans (transposeEquiv K B X)

def horizontalCurry (K B : SSet.{u}) (X : BiSSet.{u}) (f : box K B ⟶ X) :=
  horizontalBoxEquiv K B X f

def horizontalUncurry (K B : SSet.{u}) (X : BiSSet.{u})
    (f : K ⟶ horizontalMapping B X.flip) := (horizontalBoxEquiv K B X).symm f

theorem horizontalCurry_pre {K L : SSet.{u}} (i : K ⟶ L) (B : SSet.{u})
    (X : BiSSet.{u}) (f : box L B ⟶ X) :
    horizontalCurry K B X (boxMap i (𝟙 B) ≫ f) = i ≫ horizontalCurry L B X f := by
  change transpose K B X (boxCurry K B X (boxMap i (𝟙 B) ≫ f)) = _
  rw [boxCurry_pre, Category.id_comp, transpose_pre_horizontal]
  rfl

theorem horizontalCurry_value (K B : SSet.{u}) (X : BiSSet.{u}) (f : box K B ⟶ X)
    (h v : SimplexCategoryᵒᵖ) (a : K.obj h) (b : B.obj v) :
    ((horizontalCurry K B X f).app h a).app v b = (f.app h).app v (a, b) := rfl

theorem horizontalUncurry_value (K B : SSet.{u}) (X : BiSSet.{u})
    (f : K ⟶ horizontalMapping B X.flip) (h v : SimplexCategoryᵒᵖ)
    (a : K.obj h) (b : B.obj v) :
    ((horizontalUncurry K B X f).app h).app v (a, b) = (f.app h a).app v b := rfl

theorem box_glue_of_pushout {K₀ K₁ K₂ K₃ B : SSet.{u}} {X : BiSSet.{u}}
    {i : K₀ ⟶ K₁} {j : K₀ ⟶ K₂} {a : K₁ ⟶ K₃} {b : K₂ ⟶ K₃}
    (hs : IsPushout i j a b) (g₁ : box K₁ B ⟶ X) (g₂ : box K₂ B ⟶ X)
    (hg : boxMap i (𝟙 B) ≫ g₁ = boxMap j (𝟙 B) ≫ g₂) :
    ∃ g : box K₃ B ⟶ X, boxMap a (𝟙 B) ≫ g = g₁ ∧ boxMap b (𝟙 B) ≫ g = g₂ := by
  have he := congrArg (horizontalCurry K₀ B X) hg
  rw [horizontalCurry_pre, horizontalCurry_pre] at he
  let z := hs.desc (horizontalCurry K₁ B X g₁) (horizontalCurry K₂ B X g₂) he
  refine ⟨horizontalUncurry K₃ B X z, ?_, ?_⟩
  · apply (horizontalBoxEquiv K₁ B X).injective
    change horizontalCurry K₁ B X (boxMap a (𝟙 B) ≫ horizontalUncurry K₃ B X z) = _
    rw [horizontalCurry_pre]
    change a ≫ (horizontalBoxEquiv K₃ B X) ((horizontalBoxEquiv K₃ B X).symm z) = _
    rw [Equiv.apply_symm_apply]
    exact hs.inl_desc _ _ he
  · apply (horizontalBoxEquiv K₂ B X).injective
    change horizontalCurry K₂ B X (boxMap b (𝟙 B) ≫ horizontalUncurry K₃ B X z) = _
    rw [horizontalCurry_pre]
    change b ≫ (horizontalBoxEquiv K₃ B X) ((horizontalBoxEquiv K₃ B X).symm z) = _
    rw [Equiv.apply_symm_apply]
    exact hs.inr_desc _ _ he

end
end DaggerNativeBisimplicialBoxHorizontalHom
