import TopCatModelCategory.ModelCategorySSet
import Mathlib.CategoryTheory.Adjunction.Evaluation
import Mathlib.CategoryTheory.LiftingProperties.Adjunction

/-! The native right adjoint to one degree sends surjections to trivial Kan fibrations. -/
set_option autoImplicit false
open CategoryTheory Limits HomotopicalAlgebra Opposite
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerNativeDegreeEvaluationTrivialFibrations
noncomputable section

theorem injective_surjective_lifting {A B X Y : Type u} (i : A ⟶ B) (p : X ⟶ Y)
    (hi : Function.Injective i) (hp : Function.Surjective p) : HasLiftingProperty i p := by
  classical
  constructor
  intro f g sq
  refine ⟨⟨{
    l := fun b ↦ if h : ∃ a, i a = b then f h.choose else (hp (g b)).choose
    fac_left := ?_
    fac_right := ?_ }⟩⟩
  · funext a
    dsimp
    rw [dif_pos (show ∃ a', i a' = i a from ⟨a, rfl⟩)]
    congr 1
    exact hi (Exists.choose_spec (show ∃ a', i a' = i a from ⟨a, rfl⟩))
  · funext b
    dsimp
    split_ifs with h
    · have hs := congr_fun sq.w h.choose
      change p (f h.choose) = g (i h.choose) at hs
      exact hs.trans (congrArg g h.choose_spec)
    · exact (hp (g b)).choose_spec

/-- This is Mathlib's original evaluation right adjoint, with no replacement of its map. -/
theorem evaluationRightAdjoint_trivialFibration (n : SimplexCategoryᵒᵖ)
    {A B : Type u} (p : A ⟶ B) (hp : Function.Surjective p) :
    trivialFibrations SSet.{u} ((evaluationRightAdjoint (Type u) n).map p) := by
  rw [← cofibrations_rlp]
  intro X Y i hi
  have : Cofibration (C := SSet.{u}) i := (cofibration_iff i).mpr hi
  have : Mono i := (SSet.modelCategoryQuillen.cofibration_iff i).mp inferInstance
  have : Mono (i.app n) := inferInstance
  exact ((evaluationAdjunctionLeft (Type u) n).hasLiftingProperty_iff i p).mp
    (injective_surjective_lifting (i.app n) p (injective_of_mono _) hp)

end
end DaggerNativeDegreeEvaluationTrivialFibrations
