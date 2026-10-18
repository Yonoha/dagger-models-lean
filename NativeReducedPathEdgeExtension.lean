import NativeFreeGroupoidNormalPath

/-! Extending a reduced native path either stays reduced or cancels exactly its final edge. -/
set_option autoImplicit false
open CategoryTheory
open DaggerNativeSignedPathWords DaggerNativeFreeGroupoidWordLabels
open DaggerNativeFreeGroupoidNormalPath DaggerNativeSignedPathReduction
universe u
namespace DaggerNativeReducedPathEdgeExtension
noncomputable section

variable (V : Type u) [Quiver.{u + 1} V]

theorem reduced_extension_or_cancel {a b c : Quiver.Symmetrify V} (p : Quiver.Path a b)
    (hp : FreeGroup.IsReduced (word p)) (e : b ⟶ c) :
    FreeGroup.IsReduced (word (p.cons e)) ∨
      ∃ q : Quiver.Path a c, p = q.cons (Quiver.reverse e) ∧ FreeGroup.IsReduced (word q) := by
  classical
  cases p with
  | nil => exact Or.inl FreeGroup.IsReduced.singleton
  | @cons d _ q f =>
    by_cases he : letter f = letter (Quiver.reverse e)
    · obtain ⟨hd, hf⟩ := letter_same_target f (Quiver.reverse e) he
      subst d
      have hf' : f = Quiver.reverse e := eq_of_heq hf
      subst f
      refine Or.inr ⟨q, rfl, ?_⟩
      exact hp.tail
    · left
      rw [word, word, FreeGroup.isReduced_cons_cons]
      refine ⟨?_, hp⟩
      intro hsame
      by_contra hsign
      have hflip : (letter f).2 = !(letter e).2 := by
        cases h₁ : (letter f).2 <;> cases h₂ : (letter e).2 <;> simp_all
      apply he
      rw [letter_reverse]
      exact Prod.ext hsame.symm hflip

theorem norm_comp_edge_changes_by_one {a b c : Quiver.Symmetrify V}
    (f : (quotientMap V).obj a ⟶ (quotientMap V).obj b) (e : b ⟶ c) :
    norm V (f ≫ (quotientMap V).map e.toPath) = norm V f + 1 ∨
      norm V (f ≫ (quotientMap V).map e.toPath) + 1 = norm V f := by
  let p := normalPath V f
  have hp : FreeGroup.IsReduced (word p) := normalPath_reduced V f
  have he : (quotientMap V).map (p.cons e) = f ≫ (quotientMap V).map e.toPath := by
    change (quotientMap V).map (p ≫ e.toPath) = _
    rw [CategoryTheory.Functor.map_comp, quotient_normalPath]
  rcases reduced_extension_or_cancel V p hp e with hred | ⟨q, hq, hred⟩
  · left
    rw [← he, norm_of_reduced V _ hred]
    rfl
  · right
    have he' : (quotientMap V).map (p.cons e) = (quotientMap V).map q := by
      rw [hq]
      exact quotient_backtrack V q e
    rw [← he, he', norm_of_reduced V q hred]
    change q.length + 1 = p.length
    rw [hq]
    rfl

end
end DaggerNativeReducedPathEdgeExtension
