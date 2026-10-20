import Mathlib.CategoryTheory.Presentable.Basic
import Mathlib.CategoryTheory.Limits.Filtered

/-!
# Simultaneous strict equations at a cardinal-filtered stage

A finite family can have different source objects and different target diagrams.
Each whole source is cardinal-presentable; no finite-size premise is substituted.
-/
set_option autoImplicit false
open CategoryTheory Limits
universe u v w
namespace DaggerFiniteStageEquations

variable {C : Type w} [Category.{v} C] {J : Type u} [SmallCategory J]
    (κ : Cardinal.{u}) [Fact κ.IsRegular]
    [IsCardinalFiltered J κ] {A : Type u} [Finite A]
    (K : A → C) (D : A → J ⥤ C)
    (c : ∀ a, Cocone (D a)) (hc : ∀ a, IsColimit (c a))
    (hK : ∀ a, IsCardinalPresentable (K a) κ)
    {i : J} (f g : ∀ a, K a ⟶ (D a).obj i)
    (heq : ∀ a, f a ≫ (c a).ι.app i = g a ≫ (c a).ι.app i)

include κ c hc hK heq

omit [Finite A] in
theorem finite_subset (s : Finset A) :
    ∃ (j : J) (t : i ⟶ j), ∀ a ∈ s, f a ≫ (D a).map t = g a ≫ (D a).map t := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨i, 𝟙 i, by simp⟩
  | @insert a s _ ih =>
    obtain ⟨j, t, ht⟩ := ih
    have : IsCardinalPresentable (K a) κ := hK a
    have he : (f a ≫ (D a).map t) ≫ (c a).ι.app j =
        (g a ≫ (D a).map t) ≫ (c a).ι.app j := by
      simpa only [Category.assoc, (c a).w t] using heq a
    obtain ⟨k, v, hv⟩ := IsCardinalPresentable.exists_eq_of_isColimit' κ (hc a)
      (f a ≫ (D a).map t) (g a ≫ (D a).map t) he
    refine ⟨k, t ≫ v, ?_⟩
    intro b hb
    simp only [Finset.mem_insert] at hb
    rcases hb with rfl | hb
    · simpa only [Functor.map_comp, Category.assoc] using hv
    · simpa only [Functor.map_comp, Category.assoc] using
        congrArg (fun z ↦ z ≫ (D b).map v) (ht b hb)

theorem all_equations :
    ∃ (j : J) (t : i ⟶ j), ∀ a, f a ≫ (D a).map t = g a ≫ (D a).map t := by
  classical
  let _ : Fintype A := Fintype.ofFinite A
  obtain ⟨j, t, ht⟩ := finite_subset κ K D c hc hK f g heq Finset.univ
  exact ⟨j, t, fun a ↦ ht a (Finset.mem_univ a)⟩

end DaggerFiniteStageEquations
