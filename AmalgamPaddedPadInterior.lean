import AmalgamPaddedPad
import AmalgamPaddedTrimNormal

/-! Padding a normal path changes only its two endpoint identity slots.
New endpoints retain their actual B colors, including the empty-path rank-zero case. -/

open CategoryTheory DaggerModels DaggerAmalgamPresentation DaggerAmalgamReduction
open DaggerAmalgamPaddedClassification DaggerAmalgamPathMeasure

universe u
namespace DaggerAmalgamPaddedClassifier
noncomputable section
set_option autoImplicit false
variable (C B : SimplicialCat.{u, u}) (x : C.Obj) (b : B.Obj)

theorem identityFree_tail {q : SimplexCategoryᵒᵖ} (l : List (Edge C B q))
    (hi : IdentityFree C B q l) : IdentityFree C B q l.tail := by
  cases l with
  | nil => exact hi
  | cons e l => exact (identityFree_cons_iff C B e l).1 hi |>.2

theorem prefixFree_of_identityFree {q : SimplexCategoryᵒᵖ} (l : List (Edge C B q))
    (hi : IdentityFree C B q l) : PrefixFree C B l := by
  induction l with
  | nil => trivial
  | cons e l ih =>
    cases l with
    | nil => trivial
    | cons d l =>
      have hh := (identityFree_cons_iff C B e (d :: l)).1 hi
      exact ⟨hh.1, ih hh.2⟩

theorem prefixFree_startPad {q : SimplexCategoryᵒᵖ} {t : Objects C B x b}
    (c : Bool) (a : At C B q c) (p : Path C B x b q (label C B x b c a) t)
    (hi : IdentityFree C B q (encode C B x b p)) :
    PrefixFree C B (encode C B x b (startPad C B x b c a p)) := by
  classical
  by_cases hs : Starts C B x b p c
  · simpa only [startPad, if_pos hs] using prefixFree_of_identityFree C B _ hi
  · simp only [startPad, if_neg hs, encode_comp, encode_factorPath]
    exact (prefixFree_append_singleton C B _ _).2 hi

theorem middleFree_startPad {q : SimplexCategoryᵒᵖ} {t : Objects C B x b}
    (c : Bool) (a : At C B q c) (p : Path C B x b q (label C B x b c a) t)
    (hi : IdentityFree C B q (encode C B x b p)) :
    MiddleFree C B (encode C B x b (startPad C B x b c a p)) := by
  classical
  by_cases hs : Starts C B x b p c
  · simpa only [startPad, if_pos hs] using
      prefixFree_of_identityFree C B _ (identityFree_tail C B _ hi)
  · simp only [startPad, if_neg hs, encode_comp, encode_factorPath, MiddleFree]
    cases he : encode C B x b p with
    | nil => trivial
    | cons e l =>
      simp only [List.cons_append, List.tail_cons]
      apply (prefixFree_append_singleton C B _ _).2
      exact (identityFree_cons_iff C B e l).1 (he ▸ hi) |>.2

theorem middleFree_padPath {q : SimplexCategoryᵒᵖ} (c d : Bool)
    (a : At C B q c) (z : At C B q d)
    (p : Path C B x b q (label C B x b c a) (label C B x b d z))
    (hi : IdentityFree C B q (encode C B x b p)) :
    MiddleFree C B (encode C B x b (padPath C B x b c d a z p)) := by
  classical
  by_cases ht : Ends C B x b (startPad C B x b c a p) d
  · simpa only [padPath, endPad, if_pos ht] using middleFree_startPad C B x b c a p hi
  · simpa only [padPath, endPad, if_neg ht, encode_comp, encode_factorPath,
      List.singleton_append, MiddleFree, List.tail_cons] using
      prefixFree_startPad C B x b c a p hi

theorem starts_from_new {q : SimplexCategoryᵒᵖ} {s t : Objects C B x b}
    (p : Path C B x b q s t) : ∀ (z : B.Obj), z ≠ b → s = rightObj C B x b z →
      encode C B x b p ≠ [] → Starts C B x b p true := by
  letI : Quiver (Objects C B x b) :=
    SimplicialColimitsFree.Paths.quiverAt (graph C B x b) q
  induction p with
  | nil => intro z hz hs hn; exact False.elim (hn rfl)
  | cons p e ih =>
    intro z hz hs hn
    cases p with
    | nil =>
      cases hs
      simpa only [Starts, encode, firstColor] using
        congrArg some (edge_from_new_tag C B x b z hz e)
    | cons p f => exact ih z hz hs (by simp [encode])

theorem ends_at_new {q : SimplexCategoryᵒᵖ} {s t : Objects C B x b}
    (p : Path C B x b q s t) (w : B.Obj) (hw : w ≠ b) (ht : t = rightObj C B x b w)
    (hn : encode C B x b p ≠ []) : Ends C B x b p true := by
  cases p with
  | nil => exact False.elim (hn rfl)
  | cons p e =>
    cases ht
    simpa only [Ends, encode, List.head?_cons, Option.map_some] using
      congrArg some (edge_to_new_tag C B x b w hw e)

theorem count_startPad_C {q : SimplexCategoryᵒᵖ} {t : Objects C B x b}
    (a : C.Obj) (p : Path C B x b q (leftObj C B x b a) t) :
    rightCount C B x b q (startPad C B x b false a p) = rightCount C B x b q p := by
  classical
  by_cases hs : Starts C B x b p false <;>
    simp [startPad, hs, rightCount_comp, rightCount_factorPath]

theorem count_endPad_C {q : SimplexCategoryᵒᵖ} {s : Objects C B x b}
    (d : C.Obj) (p : Path C B x b q s (leftObj C B x b d)) :
    rightCount C B x b q (endPad C B x b false d p) = rightCount C B x b q p := by
  classical
  by_cases ht : Ends C B x b p false <;>
    simp [endPad, ht, rightCount_comp, rightCount_factorPath]

theorem count_padPath_OO {q : SimplexCategoryᵒᵖ} (a d : C.Obj)
    (p : Path C B x b q (leftObj C B x b a) (leftObj C B x b d)) :
    rightCount C B x b q (padPath C B x b false false a d p) =
      rightCount C B x b q p :=
  (count_endPad_C C B x b d _).trans (count_startPad_C C B x b a p)

theorem count_padPath_ON {q : SimplexCategoryᵒᵖ} (a : C.Obj) (w : B.Obj) (hw : w ≠ b)
    (p : Path C B x b q (leftObj C B x b a) (rightObj C B x b w)) :
    rightCount C B x b q (padPath C B x b false true a w p) =
      rightCount C B x b q p := by
  classical
  have hs := starts_startPad C B x b false a p
  have hn : encode C B x b (startPad C B x b false a p) ≠ [] := by
    intro he
    simp [Starts, he, firstColor] at hs
  have ht := ends_at_new C B x b _ w hw rfl hn
  simpa only [padPath, endPad, if_pos ht] using count_startPad_C C B x b a p

theorem count_padPath_NO {q : SimplexCategoryᵒᵖ} (z : B.Obj) (hz : z ≠ b) (d : C.Obj)
    (p : Path C B x b q (rightObj C B x b z) (leftObj C B x b d)) :
    rightCount C B x b q (padPath C B x b true false z d p) =
      rightCount C B x b q p := by
  classical
  have hn : encode C B x b p ≠ [] := by
    intro he
    rcases nil_or_factor_last C B x b p with ⟨s, _⟩ | ⟨c, a, v, k, pref, ht, hp⟩
    · exact hz ((leftObj_eq_rightObj_iff C B x b d z).1 s.symm).2
    · simp [hp, encode_castPath, encode_comp] at he
  have hs := starts_from_new C B x b p z hz rfl hn
  simpa only [padPath, startPad, if_pos hs] using count_endPad_C C B x b d p

theorem predCount_padPath_NN {q : SimplexCategoryᵒᵖ} (z w : B.Obj)
    (hz : z ≠ b) (hw : w ≠ b)
    (p : Path C B x b q (rightObj C B x b z) (rightObj C B x b w)) :
    (rightCount C B x b q (padPath C B x b true true z w p)).pred =
      (rightCount C B x b q p).pred := by
  classical
  by_cases hn : encode C B x b p ≠ []
  · have hs := starts_from_new C B x b p z hz rfl hn
    have ht := ends_at_new C B x b p w hw rfl hn
    simp only [padPath, startPad, if_pos hs, endPad, if_pos ht]
  · rcases nil_or_factor_last C B x b p with ⟨he, hp⟩ |
        ⟨c, a, d, k, pref, ht, hp⟩
    · have hzv := rightObj_injective C B x b he
      cases hzv
      rw [hp]
      simp [castPath, padPath, startPad, endPad, Starts, Ends, firstColor,
        rightCount_factorPath, tag]
    · exact False.elim (hn (by simp [hp, encode_castPath, encode_comp]))

end
end DaggerAmalgamPaddedClassifier
