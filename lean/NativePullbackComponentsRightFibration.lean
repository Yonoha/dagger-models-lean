import NativePullbackComponentsPiOneSurjective

/-! The same canonical component comparison when the original right leg is a fibration. -/
set_option autoImplicit false
open CategoryTheory Limits Simplicial HomotopicalAlgebra SSet SSet.KanComplex
open DaggerNativePullbackComponentsPiOneSurjective
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerNativePullbackComponentsRightFibration
noncomputable section

def componentPairSwap {E C B : SSet.{u}} (p : E ⟶ B) (q : C ⟶ B) :
    {a : E.π₀ × C.π₀ // mapπ₀ p a.1 = mapπ₀ q a.2} ≃
      {a : C.π₀ × E.π₀ // mapπ₀ q a.1 = mapπ₀ p a.2} where
  toFun a := ⟨⟨a.val.2, a.val.1⟩, a.property.symm⟩
  invFun a := ⟨⟨a.val.2, a.val.1⟩, a.property.symm⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem componentsComparison_symmetry {E C B : SSet.{u}} (p : E ⟶ B) (q : C ⟶ B) :
    componentsComparison q p ∘ mapπ₀ (pullbackSymmetry p q).hom =
      componentPairSwap p q ∘ componentsComparison p q := by
  funext s
  apply Subtype.ext
  apply Prod.ext
  · change mapπ₀ (pullback.fst q p) (mapπ₀ (pullbackSymmetry p q).hom s) =
      mapπ₀ (pullback.snd p q) s
    rw [← mapπ₀_comp_apply, pullbackSymmetry_hom_comp_fst]
  · change mapπ₀ (pullback.snd q p) (mapπ₀ (pullbackSymmetry p q).hom s) =
      mapπ₀ (pullback.fst p q) s
    rw [← mapπ₀_comp_apply, pullbackSymmetry_hom_comp_snd]

theorem componentsComparison_bijective_of_right_fibration {E C B : SSet.{u}}
    (p : E ⟶ B) (q : C ⟶ B) [Fibration q] [IsFibrant B] [IsFibrant E]
    (hq : ∀ (c : C _⦋0⦌) (b : B _⦋0⦌) (hc : q.app _ c = b),
      Function.Surjective (mapπ q 1 c b hc)) :
    Function.Bijective (componentsComparison p q) := by
  have h : Function.Bijective
      (componentsComparison q p ∘ mapπ₀ (pullbackSymmetry p q).hom) :=
    (componentsComparison_bijective q p hq).comp
      (SSet.π₀Functor.mapIso (pullbackSymmetry p q)).toEquiv.bijective
  rw [componentsComparison_symmetry] at h
  constructor
  · intro s t he
    exact h.1 (congrArg (componentPairSwap p q) he)
  · intro a
    obtain ⟨s, hs⟩ := h.2 (componentPairSwap p q a)
    exact ⟨s, (componentPairSwap p q).injective hs⟩

end
end DaggerNativePullbackComponentsRightFibration
