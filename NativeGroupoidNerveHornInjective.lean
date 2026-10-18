import NativeGroupoidTwoChainExt
import NativeHighHornRestrictionInjective

/-! Every native groupoid nerve has unique fillers for all horns of dimension at least two. -/
set_option autoImplicit false
open CategoryTheory Simplicial Opposite
open DaggerNativeGroupoidTwoChainExt DaggerNativeHighHornRestrictionInjective
universe u
namespace DaggerNativeGroupoidNerveHornInjective
noncomputable section

theorem two_horn_restriction_injective (G : Type u) [Groupoid.{u} G] (i : Fin 3)
    {f g : (Δ[2] : SSet.{u}) ⟶ nerve G}
    (h : (Λ[2, i] : (Δ[2] : SSet.{u}).Subcomplex).ι ≫ f =
      (Λ[2, i] : (Δ[2] : SSet.{u}).Subcomplex).ι ≫ g) : f = g := by
  obtain ⟨A, rfl⟩ := SSet.yonedaEquiv.symm.surjective f
  obtain ⟨B, rfl⟩ := SSet.yonedaEquiv.symm.surjective g
  apply congrArg SSet.yonedaEquiv.symm
  have hd (j : Fin 3) (hj : j ≠ i) : (nerve G).δ j A = (nerve G).δ j B := by
    have hh := congrArg SSet.yonedaEquiv (horn_face_eq i h j hj)
    exact hh
  obtain ⟨x0, x1, x2, a, b, rfl⟩ := ComposableArrows.mk₂_surjective A
  obtain ⟨y0, y1, y2, c, d, rfl⟩ := ComposableArrows.mk₂_surjective B
  fin_cases i
  · apply first_composite_ext
    · have hh := hd 2 (by decide)
      rw [nerve.δ₂_mk₂_eq, nerve.δ₂_mk₂_eq] at hh
      exact congrArg ComposableArrows.arrowEquiv hh
    · have hh := hd 1 (by decide)
      rw [nerve.δ₁_mk₂_eq, nerve.δ₁_mk₂_eq] at hh
      exact congrArg ComposableArrows.arrowEquiv hh
  · apply ComposableArrows.ext₂_of_arrow
    · have hh := hd 2 (by decide)
      rw [nerve.δ₂_mk₂_eq, nerve.δ₂_mk₂_eq] at hh
      exact congrArg ComposableArrows.arrowEquiv hh
    · have hh := hd 0 (by decide)
      rw [nerve.δ₀_mk₂_eq, nerve.δ₀_mk₂_eq] at hh
      exact congrArg ComposableArrows.arrowEquiv hh
  · apply last_composite_ext
    · have hh := hd 0 (by decide)
      rw [nerve.δ₀_mk₂_eq, nerve.δ₀_mk₂_eq] at hh
      exact congrArg ComposableArrows.arrowEquiv hh
    · have hh := hd 1 (by decide)
      rw [nerve.δ₁_mk₂_eq, nerve.δ₁_mk₂_eq] at hh
      exact congrArg ComposableArrows.arrowEquiv hh

theorem horn_restriction_injective (G : Type u) [Groupoid.{u} G] (n : ℕ)
    (i : Fin (n + 3)) {f g : (Δ[n + 2] : SSet.{u}) ⟶ nerve G}
    (h : (Λ[n + 2, i] : (Δ[n + 2] : SSet.{u}).Subcomplex).ι ≫ f =
      (Λ[n + 2, i] : (Δ[n + 2] : SSet.{u}).Subcomplex).ι ≫ g) : f = g := by
  cases n with
  | zero => exact two_horn_restriction_injective G i h
  | succ n => exact high_horn_restriction_injective n i h

end
end DaggerNativeGroupoidNerveHornInjective
