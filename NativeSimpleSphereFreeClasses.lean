import NativePiEvaluationFibreAction
import NativeFibrationComponentFibre
import NativeUnitalMultiplicationAction

/-! Existing trivial pi actions identify original based pi with the actual free-sphere fibre. -/
set_option autoImplicit false
open CategoryTheory MonoidalCategory MonoidalClosed HomotopicalAlgebra Simplicial
open SSet.KanComplex SSet.KanComplex.FundamentalGroupoid
open DaggerNativePiEvaluationFibreComponents DaggerNativePiEvaluationFibreAction
open DaggerNativeFibrationComponentFibre DaggerNativeUnitalMultiplicationAction
open DaggerOriginalFixedObjectCotensorPoints
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerNativeSimpleSphereFreeClasses
noncomputable section

theorem sphere_evaluation_action_trivial (n : ℕ) (i : Fin (n + 2))
    (a : 𝟙_ SSet.{u} ⟶ (SSet.horn (n + 1) i : SSet.{u}))
    (X : SSet.{u}) [IsFibrant X] (x : X _⦋0⦌) (hX : TrivialActionAt X x)
    (p : FundamentalGroupoid.mk x ⟶ FundamentalGroupoid.mk x)
    (c : (SSet.Subcomplex.fiber
      (pointEvaluation (a ≫ SSet.Subcomplex.homOfLE (SSet.horn_le_boundary i)) X) x :
        SSet.{u}).π₀) :
    π₀FiberAction
      (pointEvaluation (a ≫ SSet.Subcomplex.homOfLE (SSet.horn_le_boundary i)) X) p c = c := by
  obtain ⟨s, rfl⟩ := (piEvaluationFibreEquiv n i a X x).surjective c
  rw [piEvaluationFibreEquiv_action, hX n p s]

def piFreeSphereFibreEquiv (n : ℕ) (i : Fin (n + 2))
    (a : 𝟙_ SSet.{u} ⟶ (SSet.horn (n + 1) i : SSet.{u}))
    (X : SSet.{u}) [IsFibrant X] (x : X _⦋0⦌) (hX : TrivialActionAt X x) :
    π n X x ≃ {c : ((ihom (SSet.boundary (n + 1) : SSet.{u})).obj X).π₀ //
      SSet.mapπ₀ (pointEvaluation
        (a ≫ SSet.Subcomplex.homOfLE (SSet.horn_le_boundary i)) X) c = SSet.π₀.mk x} :=
  (piEvaluationFibreEquiv n i a X x).trans
    (componentFibreEquiv _ x (sphere_evaluation_action_trivial n i a X x hX))

theorem piFreeSphereFibreEquiv_val (n : ℕ) (i : Fin (n + 2))
    (a : 𝟙_ SSet.{u} ⟶ (SSet.horn (n + 1) i : SSet.{u}))
    (X : SSet.{u}) [IsFibrant X] (x : X _⦋0⦌) (hX : TrivialActionAt X x) (s : π n X x) :
    (piFreeSphereFibreEquiv n i a X x hX s).val =
      SSet.mapπ₀ (SSet.Subcomplex.fiber
        (pointEvaluation (a ≫ SSet.Subcomplex.homOfLE (SSet.horn_le_boundary i)) X) x).ι
        (piEvaluationFibreEquiv n i a X x s) := rfl

end
end DaggerNativeSimpleSphereFreeClasses
