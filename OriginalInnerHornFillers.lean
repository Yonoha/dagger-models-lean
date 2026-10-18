import Mathlib.AlgebraicTopology.Quasicategory.Basic
import OriginalDaggerCoreKanIdentity

/-!
# The literal inner-horn filling condition in arbitrary universe

The pinned native Quasicategory class is restricted to universe zero. This
predicate uses the same actual standard simplices and horn inclusions in any
universe. At universe zero it is proved equivalent to the native class.
Neither the native definition nor any dependency pin is changed.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial

universe u

namespace DaggerOriginalInnerHornFillers

/-- Fill every actual inner horn, with the exact horn inclusion, in arbitrary universe. -/
def innerHornFillers (X : SSet.{u}) : Prop :=
  ∀ {n : ℕ} {i : Fin (n + 1)}, 0 < i → i < Fin.last n →
    ∀ σ₀ : (Λ[n, i] : SSet.{u}) ⟶ X,
      ∃ σ : (Δ[n] : SSet.{u}) ⟶ X, σ₀ = Λ[n, i].ι ≫ σ

/-- In universe zero this is exactly the pinned native quasicategory property. -/
theorem innerHornFillers_iff_native_quasicategory (X : SSet.{0}) :
    innerHornFillers X ↔ X.Quasicategory := by
  constructor
  · intro h
    constructor
    intro n i σ₀ h0 hn
    exact h h0 hn σ₀
  · intro h
    have : X.Quasicategory := h
    intro n i h0 hn σ₀
    exact SSet.Quasicategory.hornFilling h0 hn σ₀

/-- The native Kan property supplies this literal inner-horn filling condition in any universe. -/
theorem innerHornFillers_of_kan (X : SSet.{u}) [X.KanComplex] : innerHornFillers X := by
  intro n i h0 hn σ₀
  cases n with
  | zero =>
    have hi := i.isLt
    change 0 < i.val at h0
    omega
  | succ n => exact SSet.KanComplex.hornFilling σ₀

end DaggerOriginalInnerHornFillers
