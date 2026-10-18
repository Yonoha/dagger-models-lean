import AmalgamPaddedTrim

/-! Exact endpoint-only normalization for alternating paths with identity-free interiors. -/

open CategoryTheory DaggerModels DaggerAmalgamPresentation DaggerAmalgamReduction
open DaggerAmalgamPaddedClassification DaggerAmalgamNormalForms

universe u
namespace DaggerAmalgamPaddedClassifier
noncomputable section
set_option autoImplicit false
variable (C B : SimplicialCat.{u, u}) (x : C.Obj) (b : B.Obj)

def PrefixFree {q : SimplexCategoryᵒᵖ} : List (Edge C B q) → Prop
  | [] => True
  | [_] => True
  | e :: d :: l => ¬ IsIdentity C B q e ∧ PrefixFree (d :: l)

def MiddleFree {q : SimplexCategoryᵒᵖ} (l : List (Edge C B q)) : Prop :=
  PrefixFree C B l.tail

theorem identityFree_cons_iff {q : SimplexCategoryᵒᵖ} (e : Edge C B q)
    (l : List (Edge C B q)) :
    IdentityFree C B q (e :: l) ↔ ¬ IsIdentity C B q e ∧ IdentityFree C B q l := by
  constructor
  · intro h
    exact ⟨h e (List.mem_cons_self ..), fun d hd ↦ h d (List.mem_cons_of_mem _ hd)⟩
  · rintro ⟨he, hl⟩ d hd
    rcases List.mem_cons.mp hd with rfl | hd
    · exact he
    · exact hl d hd

theorem prefixFree_append_singleton {q : SimplexCategoryᵒᵖ}
    (l : List (Edge C B q)) (e : Edge C B q) :
    PrefixFree C B (l ++ [e]) ↔ IdentityFree C B q l := by
  induction l with
  | nil => simp [PrefixFree, IdentityFree]
  | cons d l ih =>
    cases l with
    | nil => simp [PrefixFree, IdentityFree]
    | cons f l =>
      simpa only [List.cons_append, PrefixFree, identityFree_cons_iff] using
        and_congr_right (fun _ ↦ ih)

theorem cutHead_prefixFree {q : SimplexCategoryᵒᵖ} (l : List (Edge C B q))
    (hm : MiddleFree C B l) : PrefixFree C B (cutHead C B l) := by
  classical
  cases l with
  | nil => trivial
  | cons e l =>
    by_cases hi : IsIdentity C B q e
    · simpa only [cutHead, if_pos hi] using hm
    · simp only [cutHead, if_neg hi]
      cases l with
      | nil => trivial
      | cons d l => exact ⟨hi, hm⟩

theorem cutTail_identityFree {q : SimplexCategoryᵒᵖ} (l : List (Edge C B q))
    (hp : PrefixFree C B l) : IdentityFree C B q (cutTail C B l) := by
  classical
  induction l with
  | nil => simp [cutTail, IdentityFree]
  | cons e l ih =>
    cases l with
    | nil =>
      by_cases hi : IsIdentity C B q e <;> simp [cutTail, hi, IdentityFree]
    | cons d l => exact (identityFree_cons_iff C B e _).2 ⟨hp.1, ih hp.2⟩

theorem cutHead_alternating {q : SimplexCategoryᵒᵖ} (l : List (Edge C B q))
    (ha : Alternating C B l) : Alternating C B (cutHead C B l) := by
  classical
  cases l with
  | nil => trivial
  | cons e l =>
    by_cases hi : IsIdentity C B q e
    · simp only [cutHead, if_pos hi]
      cases l with
      | nil => trivial
      | cons d l => exact ha.2
    · simpa only [cutHead, if_neg hi] using ha

theorem cutTail_alternating {q : SimplexCategoryᵒᵖ} (l : List (Edge C B q))
    (ha : Alternating C B l) : Alternating C B (cutTail C B l) := by
  classical
  induction l with
  | nil => trivial
  | cons e l ih =>
    cases l with
    | nil =>
      by_cases hi : IsIdentity C B q e <;> simp [cutTail, hi, Alternating]
    | cons d l =>
      cases l with
      | nil =>
        by_cases hi : IsIdentity C B q d
        · simp [cutTail, hi, Alternating]
        · simpa only [cutTail, if_neg hi] using ha
      | cons f l => exact ⟨ha.1, ih ha.2⟩

/-- The normal form removes exactly the two endpoint identities when every internal letter is
  free. -/
theorem encode_normalize_middleFree {q : SimplexCategoryᵒᵖ} {s t : Objects C B x b}
    (p : Path C B x b q s t) (ha : Alternating C B (encode C B x b p))
    (hm : MiddleFree C B (encode C B x b p)) :
    encode C B x b (normalize C B x b p).val = trimEndpoints C B (encode C B x b p) := by
  obtain ⟨p', hr, he⟩ := lift_encoded_finite C B x b p
    (trimEndpoints_reduces C B (encode C B x b p))
  have hn : DaggerAmalgamPaddedClassification.Normal C B x b p' := by
    apply (normal_iff C B x b p').2
    rw [he]
    exact ⟨cutTail_identityFree C B _ (cutHead_prefixFree C B _ hm),
      cutTail_alternating C B _ (cutHead_alternating C B _ ha)⟩
  have hh : normalize C B x b p = ⟨p', hn⟩ :=
    (normalize_finite C B x b hr).trans (normalize_of_normal C B x b ⟨p', hn⟩)
  rw [hh]
  exact he

end
end DaggerAmalgamPaddedClassifier
