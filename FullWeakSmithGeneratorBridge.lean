import OriginalSmithModelRecovered
import NativeSmithRightLifting

/-! Exact full weak squares give small Smith generators and the whole weak right recognition. -/
set_option autoImplicit false
open CategoryTheory
open DaggerSmithSolutionSet
universe u v w
namespace DaggerFullWeakSmithGeneratorBridge
noncomputable section
variable {C : Type w} [Category.{v} C] [IsLocallyPresentable.{u} C]
  {I W : MorphismProperty C} [MorphismProperty.IsSmall.{u} I]
  (S : SolutionData.{u} I W)

theorem square_factor (i : I.toSet) (f : Arrow C) (hf : W f.hom) (φ : i.val ⟶ f) :
    ∃ (j : (J S).toSet) (a : i.val ⟶ j.val) (b : j.val ⟶ f), a ≫ b = φ := by
  obtain ⟨s, α, β, h⟩ := S.factor i f hf φ
  refine ⟨⟨Arrow.mk (generator S i s α), generator_mem S i s α⟩,
    intoGenerator S i s α, fromGenerator S i s α ≫ β, ?_⟩
  rw [← Category.assoc, DaggerSmithSolutionSet.square_factor]
  exact h

theorem weak_right_le : (J S).rlp ⊓ W ≤ I.rlp :=
  DaggerNativeSmithRightLifting.rlp_of_full_square_factorization I (J S) W (square_factor S)

def generatedFactorization :
    (J S).rlp.llp.FunctorialFactorizationData (J S).rlp := soaFactorization (J S)

variable [W.HasTwoOutOfThreeProperty] (hIW : I.rlp ≤ W)
include hIW

theorem generators_le : J S ≤ I.rlp.llp ⊓ W := J_le S hIW

theorem right_class_contains : I.rlp ≤ (J S).rlp := by
  have h := MorphismProperty.antitone_rlp ((generators_le S hIW).trans inf_le_left)
  simpa only [MorphismProperty.rlp_llp_rlp] using h

theorem weak_right_eq : (J S).rlp ⊓ W = I.rlp := by
  apply le_antisymm (weak_right_le S)
  intro A B f hf
  exact ⟨right_class_contains S hIW f hf, hIW f hf⟩

theorem generated_left_le : (J S).rlp.llp ≤ I.rlp.llp :=
  MorphismProperty.antitone_llp (right_class_contains S hIW)


end
end DaggerFullWeakSmithGeneratorBridge
