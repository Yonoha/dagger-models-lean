import OriginalCounitRightConeQFunctorReconciled

/-!
# Individual literal Q cofaces are injective

The standard simplex cofaces have actual degeneracy retractions. Applying
the already constructed Q functor preserves these retractions, so each
individual Q coface is monic without any necklace quotient lifting premise.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial
open DaggerOriginalCounitRightConeQFunctor

universe u

namespace DaggerOriginalCounitRightConeQCofaceInjection

noncomputable section

/-- Every standard coface has a degeneracy retraction in the actual simplex category. -/
theorem coface_has_retraction (k : ℕ) (i : Fin (k + 2)) :
    ∃ r : ⦋k + 1⦌ ⟶ ⦋k⦌, SimplexCategory.δ i ≫ r = 𝟙 ⦋k⦌ := by
  cases i using Fin.lastCases with
  | last =>
      refine ⟨SimplexCategory.σ (Fin.last k), ?_⟩
      simpa using (SimplexCategory.δ_comp_σ_succ (i := Fin.last k))
  | cast j => exact ⟨SimplexCategory.σ j, SimplexCategory.δ_comp_σ_self⟩

/-- The actual Q functor takes each coface to an injective map in every degree. -/
theorem Qcoface_app_injective (k : ℕ) (i : Fin (k + 2)) (q : SimplexCategoryᵒᵖ) :
    Function.Injective ((QFunctor.{u}.map (SimplexCategory.δ i)).app q) := by
  obtain ⟨r, hr⟩ := coface_has_retraction k i
  have hid : QFunctor.{u}.map (SimplexCategory.δ i) ≫ QFunctor.{u}.map r =
      𝟙 (QFunctor.{u}.obj ⦋k⦌) := by
    rw [← CategoryTheory.Functor.map_comp, hr]
    exact QFunctor.{u}.map_id ⦋k⦌
  intro x y h
  have hx := congrFun (NatTrans.congr_app hid q) x
  have hy := congrFun (NatTrans.congr_app hid q) y
  change (QFunctor.{u}.map r).app q
    ((QFunctor.{u}.map (SimplexCategory.δ i)).app q x) = x at hx
  change (QFunctor.{u}.map r).app q
    ((QFunctor.{u}.map (SimplexCategory.δ i)).app q y) = y at hy
  exact hx.symm.trans ((congrArg ((QFunctor.{u}.map r).app q) h).trans hy)

/-- Each individual Q coface is an actual categorical monomorphism. -/
theorem Qcoface_mono (k : ℕ) (i : Fin (k + 2)) :
    Mono (QFunctor.{u}.map (SimplexCategory.δ i)) := by
  apply (NatTrans.mono_iff_mono_app _).2
  intro q
  exact (CategoryTheory.mono_iff_injective _).2 (Qcoface_app_injective k i q)

end

end DaggerOriginalCounitRightConeQCofaceInjection
