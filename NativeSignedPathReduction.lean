import NativeFreeGroupoidWordLabels

/-! Native free-group word reductions lift to endpoint-preserving native path cancellations. -/
set_option autoImplicit false
open CategoryTheory
open DaggerNativeSignedPathWords DaggerNativeFreeGroupoidWordLabels
universe u
namespace DaggerNativeSignedPathReduction
noncomputable section

variable (V : Type u) [Quiver.{u + 1} V]

theorem quotient_reverse_edge {a b : Quiver.Symmetrify V} (e : a ⟶ b) :
    (quotientMap V).map (Quiver.reverse e).toPath =
      Groupoid.inv ((quotientMap V).map e.toPath) := rfl

theorem quotient_backtrack {a b c : Quiver.Symmetrify V} (p : Quiver.Path a c)
    (e : b ⟶ c) :
    (quotientMap V).map ((p.cons (Quiver.reverse e)).cons e) = (quotientMap V).map p := by
  change (quotientMap V).map (p ≫ (Quiver.reverse e).toPath ≫ e.toPath) = _
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp,
    quotient_reverse_edge, Groupoid.inv_comp, Category.comp_id]

theorem lift_word_step {a b : Quiver.Symmetrify V} (p : Quiver.Path a b)
    (w : List (Edge V × Bool)) (h : FreeGroup.Red.Step (word p) w) :
    ∃ q : Quiver.Path a b, word q = w ∧ (quotientMap V).map q = (quotientMap V).map p := by
  induction p generalizing w with
  | nil => exact (FreeGroup.Red.not_step_nil h).elim
  | @cons b c p e ih =>
    change FreeGroup.Red.Step (((letter e).1, (letter e).2) :: word p) w at h
    rcases FreeGroup.Red.Step.cons_left_iff.mp h with ⟨l, hl, rfl⟩ | hl
    · obtain ⟨q, hq, he⟩ := ih l hl
      refine ⟨q.cons e, congrArg (List.cons (letter e)) hq, ?_⟩
      change (quotientMap V).map (q ≫ e.toPath) = (quotientMap V).map (p ≫ e.toPath)
      rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp, he]
    · cases p with
      | nil => simp [word] at hl
      | @cons d _ r f =>
        obtain ⟨hf, hw⟩ := List.cons.inj hl
        have hf' : letter f = letter (Quiver.reverse e) := hf.trans (letter_reverse e).symm
        obtain ⟨hd, he⟩ := letter_same_target f (Quiver.reverse e) hf'
        subst d
        have he' : f = Quiver.reverse e := eq_of_heq he
        subst f
        exact ⟨r, hw, (quotient_backtrack V r e).symm⟩

end
end DaggerNativeSignedPathReduction
