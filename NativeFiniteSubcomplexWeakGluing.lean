import NativeOriginalWeakMonoPushout
import Mathlib.AlgebraicTopology.SimplicialSet.SubcomplexColimits

/-! Finite native subcomplex attachments with all pairwise overlaps in the fixed base. -/
set_option autoImplicit false
open CategoryTheory Limits Simplicial
open DaggerNativeJoyalMappingTest
universe u v
namespace DaggerNativeFiniteSubcomplexWeakGluing
noncomputable section

variable {X : SSet.{u}} {I : Type v} (A : X.Subcomplex) (F : I → X.Subcomplex)

theorem mem_finite_union (s : Finset I) (q : SimplexCategoryᵒᵖ) (x : X.obj q) :
    x ∈ (s.sup F).obj q ↔ ∃ i ∈ s, x ∈ (F i).obj q := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.sup_insert]
    change (x ∈ (F i).obj q ∨ x ∈ (s.sup F).obj q) ↔ _
    rw [ih]
    simp only [Finset.mem_insert]
    aesop

theorem weak_inclusion_congr {A A' B B' : X.Subcomplex} (ea : A = A') (eb : B = B')
    (h : A ≤ B) (h' : A' ≤ B') :
    weakCategoricalEquivalences (SSet.Subcomplex.homOfLE h) ↔
      weakCategoricalEquivalences (SSet.Subcomplex.homOfLE h') := by
  subst A'
  subst B'
  rfl

theorem intersection_union (s : Finset I) (i : I) (hi : i ∉ s)
    (overlap : ∀ i j, i ≠ j → F i ⊓ F j ≤ A) :
    F i ⊓ (A ⊔ s.sup F) = F i ⊓ A := by
  apply le_antisymm
  · intro q x hx
    rcases hx with ⟨hfi, ha | hf⟩
    · exact ⟨hfi, ha⟩
    · obtain ⟨j, hj, hxj⟩ := (mem_finite_union F s q x).mp hf
      exact ⟨hfi, overlap i j (fun h ↦ hi (h.symm ▸ hj)) q ⟨hfi, hxj⟩⟩
  · exact inf_le_inf_left _ le_sup_left

theorem finite_union_weak (s : Finset I)
    (overlap : ∀ i j, i ≠ j → F i ⊓ F j ≤ A)
    (attach : ∀ i, weakCategoricalEquivalences
      (SSet.Subcomplex.homOfLE (inf_le_left : F i ⊓ A ≤ F i))) :
    weakCategoricalEquivalences (SSet.Subcomplex.homOfLE
      (le_sup_left : A ≤ A ⊔ s.sup F)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    apply (weak_inclusion_congr rfl (by simp) _ (le_refl A)).mpr
    exact weakCategoricalEquivalences.id_mem (A : SSet.{u})
  | @insert i s hi ih =>
    let B := A ⊔ s.sup F
    have he : F i ⊓ B = F i ⊓ A := intersection_union A F s i hi overlap
    have hat : weakCategoricalEquivalences (SSet.Subcomplex.homOfLE
        (inf_le_left : F i ⊓ B ≤ F i)) := by
      exact (weak_inclusion_congr he rfl _ _).mpr (attach i)
    have sq : SSet.Subcomplex.BicartSq (F i ⊓ B) (F i) B (F i ⊔ B) := ⟨rfl, rfl⟩
    have hw : weakCategoricalEquivalences
        (SSet.Subcomplex.homOfLE (le_sup_right : B ≤ F i ⊔ B)) :=
      DaggerNativeOriginalWeakMonoPushout.weak_of_isPushout sq.isPushout hat
    have hc := weakCategoricalEquivalences.comp_mem _ _ ih hw
    have heq : A ⊔ (insert i s).sup F = F i ⊔ B := by
      rw [Finset.sup_insert]
      dsimp [B]
      ac_rfl
    apply (weak_inclusion_congr rfl heq _ (le_trans le_sup_left le_sup_right)).mpr
    exact hc

end
end DaggerNativeFiniteSubcomplexWeakGluing
