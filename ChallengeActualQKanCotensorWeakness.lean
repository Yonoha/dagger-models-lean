import OriginalCounitRightConeQRealizationAdjunctionReconciled
import OriginalFixedObjectCotensorPoints
import SSetGluing

/-! Exact weak maps on the original Q, singular, and native Kan cotensors. -/

set_option autoImplicit false
open CategoryTheory MonoidalCategory CartesianMonoidalCategory Simplicial DaggerSSetGluing
open DaggerOriginalCounitRightCone DaggerOriginalCounitRightConeQRealizationAdjunction
open DaggerOriginalFixedObjectCotensorPoints
universe u

namespace DaggerActualQKanCotensorWeaknessChallenge

def statement : Prop :=
  (∀ X Y : SSet.{u}, X.KanComplex → Y.KanComplex →
    ∀ f : X ⟶ Y, GW f → GW (singular.{u}.map f)) ∧
  (∀ K X : SSet.{u}, X.KanComplex → GW (toUnit K) → GW (constantHom K X)) ∧
  (∀ X : SSet.{u}, X.KanComplex → ∀ n : ℕ, GW (constantHom (Q.{u} n) X)) ∧
  (∀ X : SSet.{u}, X.KanComplex → ∀ n : ℕ,
    GW (singular.{u}.map (constantHom (Δ[n] : SSet.{u}) X)))

end DaggerActualQKanCotensorWeaknessChallenge
