import FiniteStageEquations

/-! Every finite family of whole maps factors at one common stage beyond a prescribed stage. -/
set_option autoImplicit false
open CategoryTheory Limits
universe u v w
namespace DaggerFiniteStageHomFactors

variable {C : Type w} [Category.{v} C] {J : Type u} [SmallCategory J]
    (κ : Cardinal.{u}) [Fact κ.IsRegular] [IsCardinalFiltered J κ]
    {A : Type u} [Finite A] (K : A → C) (D : A → J ⥤ C)
    (c : ∀ a, Cocone (D a)) (hc : ∀ a, IsColimit (c a))
    (hK : ∀ a, IsCardinalPresentable (K a) κ) (f : ∀ a, K a ⟶ (c a).pt) (i : J)
include κ hc hK

omit [Finite A] in
theorem finite_subset (s : Finset A) :
    ∃ (j : J) (_ : i ⟶ j), ∀ a ∈ s, ∃ g : K a ⟶ (D a).obj j, g ≫ (c a).ι.app j = f a := by
  classical
  have : IsFiltered J := isFiltered_of_isCardinalFiltered J κ
  induction s using Finset.induction_on with
  | empty => exact ⟨i, 𝟙 i, by simp⟩
  | @insert a s _ ih =>
    obtain ⟨j, t, ht⟩ := ih
    have : IsCardinalPresentable (K a) κ := hK a
    obtain ⟨k, g, hg⟩ := IsCardinalPresentable.exists_hom_of_isColimit κ (hc a) (f a)
    refine ⟨IsFiltered.max j k, t ≫ IsFiltered.leftToMax j k, ?_⟩
    intro b hb
    simp only [Finset.mem_insert] at hb
    rcases hb with rfl | hb
    · refine ⟨g ≫ (D b).map (IsFiltered.rightToMax j k), ?_⟩
      simpa only [Category.assoc, (c b).w] using hg
    · obtain ⟨g', hg'⟩ := ht b hb
      refine ⟨g' ≫ (D b).map (IsFiltered.leftToMax j k), ?_⟩
      simpa only [Category.assoc, (c b).w] using hg'

theorem all_homs :
    ∃ (j : J) (_ : i ⟶ j) (g : ∀ a, K a ⟶ (D a).obj j),
      ∀ a, g a ≫ (c a).ι.app j = f a := by
  classical
  let _ : Fintype A := Fintype.ofFinite A
  obtain ⟨j, t, ht⟩ := finite_subset κ K D c hc hK f i Finset.univ
  have hg : ∀ a, ∃ g : K a ⟶ (D a).obj j, g ≫ (c a).ι.app j = f a :=
    fun a ↦ ht a (Finset.mem_univ a)
  choose g hG using hg
  exact ⟨j, t, g, hG⟩

end DaggerFiniteStageHomFactors
