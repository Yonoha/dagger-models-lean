import AmalgamPaddedTrim

/-! Canonical original endpoint identity padding, without changing any path coefficient. -/

open CategoryTheory DaggerModels DaggerAmalgamPresentation DaggerAmalgamReduction
open DaggerAmalgamPaddedClassification DaggerAmalgamNormalForms

universe u
namespace DaggerAmalgamPaddedClassifier
noncomputable section
set_option autoImplicit false
variable (C B : SimplicialCat.{u, u}) (x : C.Obj) (b : B.Obj)

theorem firstColor_append_singleton {q : SimplexCategoryᵒᵖ}
    (l : List (Edge C B q)) (e : Edge C B q) :
    firstColor C B (l ++ [e]) = some e.1 := by
  induction l with
  | nil => rfl
  | cons d l ih =>
    cases l with
    | nil => rfl
    | cons f l => exact ih

theorem firstColor_cons_of_starts {q : SimplexCategoryᵒᵖ}
    (l : List (Edge C B q)) (e : Edge C B q) (c : Bool)
    (h : firstColor C B l = some c) : firstColor C B (e :: l) = some c := by
  cases l with
  | nil => cases h
  | cons d l =>
    cases l with
    | nil => exact h
    | cons f l => exact h

theorem alternating_append_singleton {q : SimplexCategoryᵒᵖ}
    (l : List (Edge C B q)) (e : Edge C B q)
    (ha : Alternating C B l) (hc : firstColor C B l ≠ some e.1) :
    Alternating C B (l ++ [e]) := by
  induction l with
  | nil => trivial
  | cons d l ih =>
    cases l with
    | nil =>
      refine ⟨?_, trivial⟩
      intro he
      exact hc (congrArg some he)
    | cons f l => exact ⟨ha.1, ih ha.2 hc⟩

theorem alternating_cons {q : SimplexCategoryᵒᵖ}
    (l : List (Edge C B q)) (e : Edge C B q)
    (ha : Alternating C B l) (hc : l.head?.map (fun d ↦ d.1) ≠ some e.1) :
    Alternating C B (e :: l) := by
  cases l with
  | nil => trivial
  | cons d l =>
    refine ⟨?_, ha⟩
    intro he
    exact hc (congrArg some he.symm)

def startPad {q : SimplexCategoryᵒᵖ} {t : Objects C B x b}
    (c : Bool) (a : At C B q c) (p : Path C B x b q (label C B x b c a) t) :
    Path C B x b q (label C B x b c a) t := by
  classical
  exact if Starts C B x b p c then p else (factorPath C B x b c q (𝟙 a)).comp p

def endPad {q : SimplexCategoryᵒᵖ} {s : Objects C B x b}
    (d : Bool) (z : At C B q d) (p : Path C B x b q s (label C B x b d z)) :
    Path C B x b q s (label C B x b d z) := by
  classical
  exact if Ends C B x b p d then p else p.comp (factorPath C B x b d q (𝟙 z))

def padPath {q : SimplexCategoryᵒᵖ} (c d : Bool) (a : At C B q c) (z : At C B q d)
    (p : Path C B x b q (label C B x b c a) (label C B x b d z)) :
    Path C B x b q (label C B x b c a) (label C B x b d z) :=
  endPad C B x b d z (startPad C B x b c a p)

theorem starts_startPad {q : SimplexCategoryᵒᵖ} {t : Objects C B x b}
    (c : Bool) (a : At C B q c) (p : Path C B x b q (label C B x b c a) t) :
    Starts C B x b (startPad C B x b c a p) c := by
  classical
  by_cases hs : Starts C B x b p c
  · simpa only [startPad, if_pos hs] using hs
  · simp only [startPad, if_neg hs]
    simp [Starts, encode_comp, firstColor_append_singleton]
    rfl

theorem ends_endPad {q : SimplexCategoryᵒᵖ} {s : Objects C B x b}
    (d : Bool) (z : At C B q d) (p : Path C B x b q s (label C B x b d z)) :
    Ends C B x b (endPad C B x b d z p) d := by
  classical
  by_cases ht : Ends C B x b p d
  · simpa only [endPad, if_pos ht] using ht
  · simp only [endPad, if_neg ht]
    simp [Ends, encode_comp]
    rfl

theorem starts_endPad {q : SimplexCategoryᵒᵖ} {s : Objects C B x b}
    (c d : Bool) (z : At C B q d) (p : Path C B x b q s (label C B x b d z))
    (hs : Starts C B x b p c) : Starts C B x b (endPad C B x b d z p) c := by
  classical
  by_cases ht : Ends C B x b p d
  · simpa only [endPad, if_pos ht] using hs
  · simpa only [endPad, if_neg ht, Starts, encode_comp, encode_factorPath,
      List.singleton_append] using firstColor_cons_of_starts C B _ (tag C B q d (𝟙 z)) c hs

theorem alternating_startPad {q : SimplexCategoryᵒᵖ} {t : Objects C B x b}
    (c : Bool) (a : At C B q c) (p : Path C B x b q (label C B x b c a) t)
    (ha : Alternating C B (encode C B x b p)) :
    Alternating C B (encode C B x b (startPad C B x b c a p)) := by
  classical
  by_cases hs : Starts C B x b p c
  · simpa only [startPad, if_pos hs] using ha
  · simpa only [startPad, if_neg hs, encode_comp, encode_factorPath] using
      alternating_append_singleton C B _ (tag C B q c (𝟙 a)) ha hs

theorem alternating_endPad {q : SimplexCategoryᵒᵖ} {s : Objects C B x b}
    (d : Bool) (z : At C B q d) (p : Path C B x b q s (label C B x b d z))
    (ha : Alternating C B (encode C B x b p)) :
    Alternating C B (encode C B x b (endPad C B x b d z p)) := by
  classical
  by_cases ht : Ends C B x b p d
  · simpa only [endPad, if_pos ht] using ha
  · simpa only [endPad, if_neg ht, encode_comp, encode_factorPath, List.singleton_append]
      using alternating_cons C B _ (tag C B q d (𝟙 z)) ha ht

theorem padPath_starts_ends {q : SimplexCategoryᵒᵖ} (c d : Bool)
    (a : At C B q c) (z : At C B q d)
    (p : Path C B x b q (label C B x b c a) (label C B x b d z)) :
    Starts C B x b (padPath C B x b c d a z p) c ∧
      Ends C B x b (padPath C B x b c d a z p) d :=
  ⟨starts_endPad C B x b c d z _ (starts_startPad C B x b c a p),
    ends_endPad C B x b d z _⟩

theorem padPath_alternating {q : SimplexCategoryᵒᵖ} (c d : Bool)
    (a : At C B q c) (z : At C B q d)
    (p : Path C B x b q (label C B x b c a) (label C B x b d z))
    (ha : Alternating C B (encode C B x b p)) :
    Alternating C B (encode C B x b (padPath C B x b c d a z p)) :=
  alternating_endPad C B x b d z _ (alternating_startPad C B x b c a p ha)

theorem remove_start_identity {q : SimplexCategoryᵒᵖ} {t : Objects C B x b}
    (c : Bool) (a : At C B q c) (p : Path C B x b q (label C B x b c a) t) :
    Red C B x b q _ _ ((factorPath C B x b c q (𝟙 a)).comp p) p := by
  apply (red_iff_encoded C B x b).2
  simpa only [encode_comp, encode_factorPath, List.append_nil] using
    listRed_append_left (encode C B x b p) (ListRed.delete _ [] (IsIdentity.intro c a))

theorem remove_end_identity {q : SimplexCategoryᵒᵖ} {s : Objects C B x b}
    (d : Bool) (z : At C B q d) (p : Path C B x b q s (label C B x b d z)) :
    Red C B x b q _ _ (p.comp (factorPath C B x b d q (𝟙 z))) p := by
  apply (red_iff_encoded C B x b).2
  simpa only [encode_comp, encode_factorPath, List.singleton_append] using
    ListRed.delete _ (encode C B x b p) (IsIdentity.intro d z)

theorem startPad_reduces {q : SimplexCategoryᵒᵖ} {t : Objects C B x b}
    (c : Bool) (a : At C B q c) (p : Path C B x b q (label C B x b c a) t) :
    Relation.ReflTransGen (Red C B x b q _ _) (startPad C B x b c a p) p := by
  classical
  by_cases hs : Starts C B x b p c
  · simp only [startPad, if_pos hs]
    exact .refl
  · simpa only [startPad, if_neg hs] using
      Relation.ReflTransGen.single (remove_start_identity C B x b c a p)

theorem endPad_reduces {q : SimplexCategoryᵒᵖ} {s : Objects C B x b}
    (d : Bool) (z : At C B q d) (p : Path C B x b q s (label C B x b d z)) :
    Relation.ReflTransGen (Red C B x b q _ _) (endPad C B x b d z p) p := by
  classical
  by_cases ht : Ends C B x b p d
  · simp only [endPad, if_pos ht]
    exact .refl
  · simpa only [endPad, if_neg ht] using
      Relation.ReflTransGen.single (remove_end_identity C B x b d z p)

theorem padPath_reduces {q : SimplexCategoryᵒᵖ} (c d : Bool)
    (a : At C B q c) (z : At C B q d)
    (p : Path C B x b q (label C B x b c a) (label C B x b d z)) :
    Relation.ReflTransGen (Red C B x b q _ _) (padPath C B x b c d a z p) p :=
  (endPad_reduces C B x b d z _).trans (startPad_reduces C B x b c a p)

theorem normalize_padPath {q : SimplexCategoryᵒᵖ} (c d : Bool)
    (a : At C B q c) (z : At C B q d)
    (p : Path C B x b q (label C B x b c a) (label C B x b d z)) :
    normalize C B x b (padPath C B x b c d a z p) = normalize C B x b p :=
  normalize_finite C B x b (padPath_reduces C B x b c d a z p)

end
end DaggerAmalgamPaddedClassifier
