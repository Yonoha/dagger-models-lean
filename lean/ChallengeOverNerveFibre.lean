import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.CategoryTheory.ComposableArrows.Basic

set_option autoImplicit false
open CategoryTheory
universe u
namespace ChallengeOverNerveFibre

/-- A chain over the constant X-chain is a unique constant chain at an arrow X→Y. -/
def Statement : Prop :=
  ∀ (T : Type u) [Category.{u} T] (x y : T) (n : ℕ) (A : Fin (n + 1) ⥤ Over y),
    A ⋙ Over.forget y = (Functor.const (Fin (n + 1))).obj x →
      ∃! f : x ⟶ y, A = (Functor.const (Fin (n + 1))).obj (Over.mk f)

end ChallengeOverNerveFibre
