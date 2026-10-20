import NativePiEvaluationFibreComponents
import NativeHornActionEvaluationPath
import NativeKanPointEvaluationFibration

/-! The original pi_n/evaluation-fibre equivalence preserves the existing native path actions. -/
set_option autoImplicit false
open CategoryTheory MonoidalCategory MonoidalClosed HomotopicalAlgebra Simplicial
open SSet.KanComplex SSet.KanComplex.FundamentalGroupoid
open DaggerNativePiEvaluationFibreComponents DaggerNativeHornActionEvaluationPath
open DaggerOriginalFixedObjectCotensorPoints
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerNativePiEvaluationFibreAction
noncomputable section

theorem piEvaluationFibreEquiv_action (n : ℕ) (i : Fin (n + 2))
    (a : 𝟙_ SSet.{u} ⟶ (SSet.horn (n + 1) i : SSet.{u}))
    (X : SSet.{u}) [IsFibrant X] {x y : X _⦋0⦌}
    (p : FundamentalGroupoid.mk x ⟶ FundamentalGroupoid.mk y) (s : π n X x) :
    π₀FiberAction
        (pointEvaluation (a ≫ SSet.Subcomplex.homOfLE (SSet.horn_le_boundary i)) X) p
        (piEvaluationFibreEquiv n i a X x s) =
      piEvaluationFibreEquiv n i a X y (action.map p s) := by
  obtain ⟨p, rfl⟩ := FundamentalGroupoid.homMk_surjective p
  obtain ⟨s, rfl⟩ := π.mk_surjective s
  obtain ⟨t, ⟨h⟩⟩ := action.exists_actionStruct p s
  rw [action.map_eq h]
  obtain ⟨v₀, h₀H, h₀F, he₀⟩ := piEvaluationFibreEquiv_mk_lift n i a X x s
  obtain ⟨v₁, h₁H, h₁F, he₁⟩ := piEvaluationFibreEquiv_mk_lift n i a X y t
  rw [he₀, he₁]
  apply (π₀FiberAction_mk_eq_iff _ p v₀ v₁).mpr
  exact ⟨evaluationActionStruct i a h v₀.val v₁.val h₀H h₀F h₁H h₁F⟩

end
end DaggerNativePiEvaluationFibreAction
