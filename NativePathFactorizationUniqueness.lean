import Mathlib.CategoryTheory.PathCategory.Basic

/-! Native path factorizations of a fixed length determine the intermediate object as well. -/
set_option autoImplicit false
open CategoryTheory
universe u
namespace DaggerNativePathFactorizationUniqueness

variable {V : Type u} [Quiver.{u + 1} V]

theorem split_unique_of_suffix_length {a b c d : V}
    (p : Quiver.Path a b) (q : Quiver.Path b d)
    (p' : Quiver.Path a c) (q' : Quiver.Path c d)
    (hq : q.length = q'.length) (h : p.comp q = p'.comp q') :
    b = c ∧ HEq p p' ∧ HEq q q' := by
  induction q generalizing c with
  | nil =>
    cases q' with
    | nil => exact ⟨rfl, heq_of_eq h, HEq.rfl⟩
    | cons q' g' => simp at hq
  | @cons x y q g ih =>
    cases q' with
    | nil => simp at hq
    | @cons x' y' q' g' =>
      have hx := Quiver.Path.obj_eq_of_cons_eq_cons h
      subst x'
      have hpq := eq_of_heq (Quiver.Path.heq_of_cons_eq_cons h)
      have hg := Quiver.Path.hom_heq_of_cons_eq_cons h
      have hq' : q.length = q'.length := by
        simpa only [Quiver.Path.length_cons, Nat.add_right_cancel_iff] using hq
      obtain ⟨hc, hp, hr⟩ := ih p' q' hq' hpq
      subst c
      cases eq_of_heq hr
      cases eq_of_heq hg
      exact ⟨rfl, hp, HEq.rfl⟩

theorem split_unique_of_prefix_length {a b c d : V}
    (p : Quiver.Path a b) (q : Quiver.Path b d)
    (p' : Quiver.Path a c) (q' : Quiver.Path c d)
    (hp : p.length = p'.length) (h : p.comp q = p'.comp q') :
    b = c ∧ HEq p p' ∧ HEq q q' := by
  have hl := congrArg Quiver.Path.length h
  simp only [Quiver.Path.length_comp, hp] at hl
  exact split_unique_of_suffix_length p q p' q' (Nat.add_left_cancel hl) h

end DaggerNativePathFactorizationUniqueness
