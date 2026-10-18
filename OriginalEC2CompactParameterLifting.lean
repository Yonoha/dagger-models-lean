import OriginalEC2CompactParameterHomEquiv
import Mathlib.CategoryTheory.LiftingProperties.Basic

/-!
# Lifting for the original EC₂ compact-open mapping arrow

For generated locally compact parameter spaces, lifting against the literal
postcomposition map is equivalent to equivariant lifting against the original
EC₂ product arrow. This supplies the actual lifting bridge, without assuming
that product arrows belong to a model class or that weak equivalences are preserved.
-/

set_option autoImplicit false

open CategoryTheory Topology DaggerModels
open DaggerOriginalDaggerRealizationC2Action DaggerOriginalCompactGeneration
open DaggerOriginalEC2HomotopyFixedPointFunctor DaggerOriginalEC2CompactParameterHomEquiv

universe u

namespace DaggerOriginalEC2CompactParameterLifting

noncomputable section

/-- The original mapping arrow and EC₂ product arrow have exactly corresponding lifting problems. -/
theorem originalEC2_lifting_iff {A B : TopCat.{u}}
    [IsGeneratedBy compactHausFamily.{u} A] [LocallyCompactSpace A]
    [IsGeneratedBy compactHausFamily.{u} B] [LocallyCompactSpace B]
    (i : A ⟶ B) {X Y : ContAction TopCat.{u} C2.{u}} (p : X ⟶ Y) :
    HasLiftingProperty (originalEC2TensorMap i) p.hom ↔
      HasLiftingProperty i (postcompose p) := by
  constructor
  · intro h
    have : HasLiftingProperty (originalEC2TensorMap i) p.hom := h
    refine ⟨?_⟩
    intro a b sq
    let a' := (originalEC2HomEquiv A X).symm a
    let b' := (originalEC2HomEquiv B Y).symm b
    have sq' : CommSq a' (originalEC2TensorMap i) p.hom b' := ⟨by
      apply (originalEC2HomEquiv A Y).injective
      rw [originalEC2HomEquiv_target_naturality, originalEC2HomEquiv_parameter_naturality]
      simpa only [a', b', Equiv.apply_symm_apply] using sq.w⟩
    refine ⟨⟨{ l := originalEC2HomEquiv B X sq'.lift, fac_left := ?_, fac_right := ?_ }⟩⟩
    · rw [← originalEC2HomEquiv_parameter_naturality, sq'.fac_left]
      exact (originalEC2HomEquiv A X).apply_symm_apply a
    · rw [← originalEC2HomEquiv_target_naturality, sq'.fac_right]
      exact (originalEC2HomEquiv B Y).apply_symm_apply b
  · intro h
    have : HasLiftingProperty i (postcompose p) := h
    refine ⟨?_⟩
    intro a b sq
    have sq' : CommSq (originalEC2HomEquiv A X a) i (postcompose p)
        (originalEC2HomEquiv B Y b) := ⟨by
      rw [← originalEC2HomEquiv_target_naturality,
        ← originalEC2HomEquiv_parameter_naturality, sq.w]⟩
    refine ⟨⟨
      { l := (originalEC2HomEquiv B X).symm sq'.lift
        fac_left := ?_
        fac_right := ?_ }⟩⟩
    · apply (originalEC2HomEquiv A X).injective
      rw [originalEC2HomEquiv_parameter_naturality, Equiv.apply_symm_apply, sq'.fac_left]
    · apply (originalEC2HomEquiv B Y).injective
      rw [originalEC2HomEquiv_target_naturality, Equiv.apply_symm_apply, sq'.fac_right]

end

end DaggerOriginalEC2CompactParameterLifting
