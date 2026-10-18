import AmalgamPaddedCritical
import AmalgamPaddedAlternation

/-! Exact full normalized encodings for all four interiors.
Only original endpoint identities are removed; internal coordinate maps remain literal. -/

open CategoryTheory DaggerModels DaggerAmalgamPresentation DaggerAmalgamReduction
open DaggerAmalgamPaddedClassification DaggerAmalgamNormalForms

universe u
namespace DaggerAmalgamPaddedClassifier
noncomputable section
set_option autoImplicit false
variable (C B : SimplicialCat.{u, u}) (x : C.Obj) (b : B.Obj)

theorem trimEndpoints_singleton {q : SimplexCategoryᵒᵖ} (e : Edge C B q) :
    trimEndpoints C B [e] = singletonTrim C B e := by
  classical
  by_cases hi : IsIdentity C B q e <;>
    simp [trimEndpoints, cutHead, cutTail, singletonTrim, hi]

theorem trimEndpoints_two_tags {q : SimplexCategoryᵒᵖ}
    (e f : Edge C B q) (l : List (Edge C B q)) :
    trimEndpoints C B (e :: (l ++ [f])) = singletonTrim C B e ++ l ++ singletonTrim C B f := by
  classical
  by_cases hi : IsIdentity C B q e
  · simp only [trimEndpoints, cutHead, if_pos hi, cutTail_append_singleton,
      singletonTrim, List.nil_append]
  · simp only [trimEndpoints, cutHead, if_neg hi]
    change cutTail C B ((e :: l) ++ [f]) = _
    rw [cutTail_append_singleton]
    simp only [singletonTrim, if_neg hi, List.cons_append, List.nil_append]

theorem normalize_decodeOO_encode (q : SimplexCategoryᵒᵖ) (a d : C.Obj) (n : ℕ)
    (h : RawOO C B x b q a d (n + 1)) (hi : ¬ criticalOO C B x b q a d (n + 1) h) :
    encode C B x b (normalize C B x b (decodeOO C B x b q a d (n + 1) h)).val =
      trimmedTag C B q false h.2.2.2 ++
        (tag C B q true (h.2.1 (Fin.last n)) :: encode C B x b
          (zig C B x b q n (fun i ↦ h.2.1 i.castSucc) h.2.2.1)) ++
            trimmedTag C B q false h.1 := by
  rw [encode_normalize_middleFree C B x b _
    (alternating_decodeOO C B x b q a d (n + 1) h)
    ((middleFree_decodeOO_iff C B x b q a d (n + 1) h).2 hi)]
  simpa only [decodeOO, encode_comp, encode_factorPath, encode_bLoop,
    List.singleton_append, List.cons_append, List.nil_append, trimmedTag, singletonTrim] using
    trimEndpoints_two_tags C B (tag C B q false h.2.2.2) (tag C B q false h.1)
      (tag C B q true (h.2.1 (Fin.last n)) :: encode C B x b
        (zig C B x b q n (fun i ↦ h.2.1 i.castSucc) h.2.2.1))

theorem normalize_decodeON_encode (q : SimplexCategoryᵒᵖ) (a : C.Obj)
    (w : B.Obj) (hw : w ≠ b) (r : ℕ) (h : RawON C B x b q a w r)
    (hi : ¬ criticalON C B x b q a w r h) :
    encode C B x b (normalize C B x b (decodeON C B x b q a w r h)).val =
      tag C B q true h.2.2.2 ::
        (encode C B x b (zig C B x b q r h.2.1 h.2.2.1) ++ trimmedTag C B q false h.1) := by
  rw [encode_normalize_middleFree C B x b _
    (alternating_decodeON C B x b q a w r h)
    ((middleFree_decodeON_iff C B x b q a w r h).2 hi)]
  have ht := trimEndpoints_two_tags C B (tag C B q true h.2.2.2) (tag C B q false h.1)
    (encode C B x b (zig C B x b q r h.2.1 h.2.2.1))
  simpa only [decodeON, encode_comp, encode_factorPath, encode_bEnd,
    List.singleton_append, singletonTrim, if_neg (new_end_not_identity C B b q w hw _),
    List.cons_append, List.nil_append, trimmedTag] using ht

theorem normalize_decodeNO_encode (q : SimplexCategoryᵒᵖ) (z : B.Obj)
    (hz : z ≠ b) (d : C.Obj) (r : ℕ) (h : RawNO C B x b q z d r)
    (hi : ¬ criticalNO C B x b q z d r h) :
    encode C B x b (normalize C B x b (decodeNO C B x b q z d r h)).val =
      trimmedTag C B q false h.2.2.2 ++
        (encode C B x b (zag C B x b q r h.2.1 h.2.2.1) ++ [tag C B q true h.1]) := by
  rw [encode_normalize_middleFree C B x b _
    (alternating_decodeNO C B x b q z d r h)
    ((middleFree_decodeNO_iff C B x b q z d r h).2 hi)]
  have ht := trimEndpoints_two_tags C B (tag C B q false h.2.2.2) (tag C B q true h.1)
    (encode C B x b (zag C B x b q r h.2.1 h.2.2.1))
  simpa only [decodeNO, encode_comp, encode_factorPath, encode_bStart,
    List.singleton_append, singletonTrim, if_neg (new_start_not_identity C B b q z hz _),
    List.append_assoc, trimmedTag] using ht

theorem normalize_decodeNN_encode (q : SimplexCategoryᵒᵖ) (z w : B.Obj)
    (hz : z ≠ b) (hw : w ≠ b) (n : ℕ) (h : RawNN C B x b q z w (n + 1))
    (hi : ¬ criticalNN C B x b q z w (n + 1) h) :
    encode C B x b (normalize C B x b (decodeNN C B x b q z w (n + 1) h)).val =
      encode C B x b (decodeNN C B x b q z w (n + 1) h) := by
  rw [encode_normalize_middleFree C B x b _
    (alternating_decodeNN C B x b q z w (n + 1) h)
    ((middleFree_decodeNN_iff C B x b q z w (n + 1) h).2 hi)]
  have ht := trimEndpoints_two_tags C B (tag C B q true h.2.2.2) (tag C B q true h.1)
    (tag C B q false (h.2.1 (Fin.last n)) :: encode C B x b
      (zag C B x b q n (fun i ↦ h.2.1 i.castSucc) h.2.2.1))
  simpa only [decodeNN, encode_comp, encode_factorPath, encode_bStart, encode_bEnd,
    List.singleton_append, List.cons_append, List.nil_append, singletonTrim,
    if_neg (new_start_not_identity C B b q z hz _),
    if_neg (new_end_not_identity C B b q w hw _)] using ht

end
end DaggerAmalgamPaddedClassifier
