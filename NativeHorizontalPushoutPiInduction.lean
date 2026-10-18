import NativeHorizontalPiGluing
import NativeHorizontalPiRebasedRestriction
import NativeHorizontalPushoutPositivePi

/-! The exact positive-pi family comparison propagates across actual horizontal pushouts. -/
set_option autoImplicit false
open CategoryTheory Limits HomotopicalAlgebra Simplicial Opposite SSet.KanComplex
open DaggerNativeBisimplicialHorizontalMapping DaggerNativeHorizontalPiCompatibility
open DaggerNativeHorizontalPiSections DaggerNativeHorizontalPiRestriction
open DaggerNativeHorizontalPiRebasedRestriction DaggerNativeHorizontalPiGluing
open DaggerNativeHorizontalPushoutPositivePi
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerNativeHorizontalPushoutPiInduction
noncomputable section

variable {K₀ K₁ K₂ K₃ : SSet.{u}} {i : K₀ ⟶ K₁} {j : K₀ ⟶ K₂}
  {a : K₁ ⟶ K₃} {b : K₂ ⟶ K₃} (h : IsPushout i j a b) (X : BiSSet.{u})
  [Fibration (horizontalPre i X)] [IsFibrant (horizontalMapping K₀ X)]
  [IsFibrant (horizontalMapping K₂ X)]
  (v : (horizontalMapping K₃ X) _⦋0⦌) (n : ℕ)

include h in
theorem piComparison_surjective_of_pushout
    (h₀ : Function.Injective (piComparison K₀ X (n + 1)
      (restrictedVertex j X (restrictedVertex b X v))))
    (h₁ : Function.Surjective (piComparison K₁ X (n + 1) (restrictedVertex a X v)))
    (h₂ : Function.Surjective (piComparison K₂ X (n + 1) (restrictedVertex b X v))) :
    Function.Surjective (piComparison K₃ X (n + 1) v) := by
  intro r
  obtain ⟨s₁, hs₁⟩ := h₁ (restrictFamily a X (n + 1) v r)
  obtain ⟨s₂, hs₂⟩ := h₂ (restrictFamily b X (n + 1) v r)
  have hc : mapπ (horizontalPre i X) (n + 1) _ _ (restrictionEquation h X v) s₁ =
      mapπ (horizontalPre j X) (n + 1) _ _ rfl s₂ := by
    apply h₀
    apply familyMap_injective K₀ X (n + 1)
    calc
      _ = i ≫ familyMap K₁ X (n + 1) (restrictedVertex a X v)
          (piComparison K₁ X (n + 1) (restrictedVertex a X v) s₁) :=
        familyMap_piComparison_restrict i X (n + 1) (restrictedVertex a X v)
          (restrictedVertex j X (restrictedVertex b X v)) (restrictionEquation h X v) s₁
      _ = i ≫ familyMap K₁ X (n + 1) (restrictedVertex a X v)
          (restrictFamily a X (n + 1) v r) := by rw [hs₁]
      _ = j ≫ familyMap K₂ X (n + 1) (restrictedVertex b X v)
          (restrictFamily b X (n + 1) v r) :=
        (gluingComparison h X (n + 1) v r).property
      _ = j ≫ familyMap K₂ X (n + 1) (restrictedVertex b X v)
          (piComparison K₂ X (n + 1) (restrictedVertex b X v) s₂) := by rw [hs₂]
      _ = _ := (familyMap_piComparison_restrict j X (n + 1) (restrictedVertex b X v)
        (restrictedVertex j X (restrictedVertex b X v)) rfl s₂).symm
  obtain ⟨z, hz⟩ := comparison_surjective h X v n ⟨⟨s₁, s₂⟩, hc⟩
  have hz₁ := congrArg (fun w ↦ w.val.1) hz
  have hz₂ := congrArg (fun w ↦ w.val.2) hz
  simp only [comparison] at hz₁ hz₂
  refine ⟨z, gluingComparison_injective h X (n + 1) v ?_⟩
  apply Subtype.ext
  apply Prod.ext
  · change restrictFamily a X (n + 1) v (piComparison K₃ X (n + 1) v z) = _
    exact (piComparison_restrict a X (n + 1) v z).symm.trans
      ((congrArg (piComparison K₁ X (n + 1) (restrictedVertex a X v)) hz₁).trans hs₁)
  · change restrictFamily b X (n + 1) v (piComparison K₃ X (n + 1) v z) = _
    exact (piComparison_restrict b X (n + 1) v z).symm.trans
      ((congrArg (piComparison K₂ X (n + 1) (restrictedVertex b X v)) hz₂).trans hs₂)

include h in
theorem piComparison_injective_of_pushout
    (h₁ : Function.Injective (piComparison K₁ X (n + 1) (restrictedVertex a X v)))
    (h₂ : Function.Injective (piComparison K₂ X (n + 1) (restrictedVertex b X v)))
    (hp : Function.Surjective
      (mapπ (horizontalPre i X) (n + 2) _ _ (restrictionEquation h X v))) :
    Function.Injective (piComparison K₃ X (n + 1) v) := by
  intro s r he
  apply (comparison_bijective h X v n hp).injective
  apply Subtype.ext
  apply Prod.ext
  · apply h₁
    exact (piComparison_restrict a X (n + 1) v s).trans
      ((congrArg (restrictFamily a X (n + 1) v) he).trans
        (piComparison_restrict a X (n + 1) v r).symm)
  · apply h₂
    exact (piComparison_restrict b X (n + 1) v s).trans
      ((congrArg (restrictFamily b X (n + 1) v) he).trans
        (piComparison_restrict b X (n + 1) v r).symm)

include h in
theorem piComparison_bijective_of_pushout
    (h₀ : Function.Injective (piComparison K₀ X (n + 1)
      (restrictedVertex j X (restrictedVertex b X v))))
    (h₁ : Function.Bijective (piComparison K₁ X (n + 1) (restrictedVertex a X v)))
    (h₂ : Function.Bijective (piComparison K₂ X (n + 1) (restrictedVertex b X v)))
    (hp : Function.Surjective
      (mapπ (horizontalPre i X) (n + 2) _ _ (restrictionEquation h X v))) :
    Function.Bijective (piComparison K₃ X (n + 1) v) :=
  ⟨piComparison_injective_of_pushout h X v n h₁.1 h₂.1 hp,
    piComparison_surjective_of_pushout h X v n h₀ h₁.2 h₂.2⟩

include h in
theorem piComparison_bijective_of_anodyne_pushout [Cofibration i] [WeakEquivalence i]
    [Fibration (C := SSet.{u}) (rowProjection X (n + 2))]
    (h₀ : Function.Injective (piComparison K₀ X (n + 1)
      (restrictedVertex j X (restrictedVertex b X v))))
    (h₁ : Function.Bijective (piComparison K₁ X (n + 1) (restrictedVertex a X v)))
    (h₂ : Function.Bijective (piComparison K₂ X (n + 1) (restrictedVertex b X v)))
    (h₀' : Function.Injective (piComparison K₀ X (n + 2)
      (restrictedVertex j X (restrictedVertex b X v))))
    (h₁' : Function.Surjective (piComparison K₁ X (n + 2) (restrictedVertex a X v))) :
    Function.Bijective (piComparison K₃ X (n + 1) v) := by
  apply piComparison_bijective_of_pushout h X v n h₀ h₁ h₂
  exact restriction_mapπ_surjective_rebased i X (n + 2)
    (restrictedVertex a X v) (restrictedVertex j X (restrictedVertex b X v))
    (restrictionEquation h X v) h₁' h₀'

end
end DaggerNativeHorizontalPushoutPiInduction
