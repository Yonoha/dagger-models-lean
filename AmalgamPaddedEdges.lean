import AmalgamPaddedCount

/-! Original factor-edge decomposition with literal source/target transports.
This uses actual dependent paths, not an arbitrary list of tags. -/

open CategoryTheory DaggerModels DaggerAmalgamPresentation DaggerAmalgamReduction
open DaggerAmalgamPaddedClassification DaggerAmalgamPathMeasure

universe u

namespace DaggerAmalgamPaddedClassifier

noncomputable section
set_option autoImplicit false

variable (C B : SimplicialCat.{u, u}) (x : C.Obj) (b : B.Obj)

theorem encode_castPath {q : SimplexCategoryᵒᵖ} {s t s' t' : Objects C B x b}
    (hs : s = s') (ht : t = t') (p : Path C B x b q s t) :
    encode C B x b (castPath C B x b hs ht p) = encode C B x b p := by
  cases hs
  cases ht
  rfl

theorem identity_tag_objects {q : SimplexCategoryᵒᵖ} (c : Bool)
    {a d : At C B q c} {h : a ⟶ d} (hi : IsIdentity C B q (tag C B q c h)) : a = d := by
  cases hi
  rfl

theorem tag_injective (q : SimplexCategoryᵒᵖ) (c : Bool) (a d : At C B q c) :
    Function.Injective (tag C B q c : (a ⟶ d) → Edge C B q) := by
  intro h k he
  simpa only [tag, Sigma.mk.inj_iff, heq_eq_eq, true_and] using he

theorem trimmedTag_injective (q : SimplexCategoryᵒᵖ) (c : Bool) (a d : At C B q c) :
    Function.Injective (trimmedTag C B q c : (a ⟶ d) → List (Edge C B q)) := by
  classical
  intro h k he
  by_cases hh : IsIdentity C B q (tag C B q c h)
  · by_cases hk : IsIdentity C B q (tag C B q c k)
    · cases hh
      cases hk
      rfl
    · simp [trimmedTag, hh, hk] at he
  · by_cases hk : IsIdentity C B q (tag C B q c k)
    · simp [trimmedTag, hh, hk] at he
    · apply tag_injective C B q c a d
      simpa only [trimmedTag, if_neg hh, if_neg hk, List.cons.injEq, and_true] using he

theorem new_start_not_identity (q : SimplexCategoryᵒᵖ) (z : B.Obj) (hz : z ≠ b)
    (h : (z ⟶[SSet] b).obj q) : ¬ IsIdentity C B q (tag C B q true h) := by
  intro hi
  exact hz (identity_tag_objects C B true hi)

theorem new_end_not_identity (q : SimplexCategoryᵒᵖ) (w : B.Obj) (hw : w ≠ b)
    (h : (b ⟶[SSet] w).obj q) : ¬ IsIdentity C B q (tag C B q true h) := by
  intro hi
  exact hw (identity_tag_objects C B true hi).symm

/-- Every actual nonempty path has an original last factor arrow, with both transports. -/
theorem nil_or_factor_last {q : SimplexCategoryᵒᵖ} {s t : Objects C B x b}
    (p : Path C B x b q s t) :
    (∃ ht : s = t, p = castPath C B x b rfl ht (.nil : Path C B x b q s s)) ∨
      ∃ (c : Bool) (a d : At C B q c) (h : a ⟶ d)
        (v : Path C B x b q s (label C B x b c a)) (ht : label C B x b c d = t),
        p = castPath C B x b rfl ht (v.comp (factorPath C B x b c q h)) := by
  cases p with
  | nil => exact Or.inl ⟨rfl, rfl⟩
  | cons p e =>
    rcases e with ⟨⟨c, a, d, h⟩, hs, ht⟩
    dsimp [source, target] at hs ht
    cases hs
    cases ht
    exact Or.inr ⟨c, a, d, h, p, rfl, rfl⟩

/-- A new B-labelled endpoint is never the target of a C edge. -/
theorem edge_to_new_tag {q : SimplexCategoryᵒᵖ} {s : Objects C B x b}
    (w : B.Obj) (hw : w ≠ b) (e : (graphHom C B x b s (rightObj C B x b w)).obj q) :
    e.val.1 = true := by
  rcases e with ⟨⟨c, a, d, h⟩, hs, ht⟩
  cases c with
  | false =>
    exact False.elim (hw ((leftObj_eq_rightObj_iff C B x b d w).1 ht).2)
  | true => rfl

/-- Likewise every original first edge from a new B-labelled object has B color. -/
theorem edge_from_new_tag {q : SimplexCategoryᵒᵖ} {t : Objects C B x b}
    (z : B.Obj) (hz : z ≠ b) (e : (graphHom C B x b (rightObj C B x b z) t).obj q) :
    e.val.1 = true := by
  rcases e with ⟨⟨c, a, d, h⟩, hs, ht⟩
  cases c with
  | false =>
    exact False.elim (hz ((leftObj_eq_rightObj_iff C B x b a z).1 hs).2)
  | true => rfl

end
end DaggerAmalgamPaddedClassifier
