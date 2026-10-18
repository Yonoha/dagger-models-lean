import AmalgamPaddedRaw
import AmalgamReductionDiamond
import NormalFormQuotient

/-! Normal original dependent paths are exactly identity-free alternating tagged paths.
The existing snoc-reversed encoding and literal contextual relation are retained. -/

open CategoryTheory DaggerModels DaggerAmalgamPresentation DaggerAmalgamReduction

universe u

namespace DaggerAmalgamPaddedClassification

noncomputable section
set_option autoImplicit false

variable (C B : SimplicialCat.{u, u}) (x : C.Obj) (b : B.Obj)

/-- The existing generic predicate on exactly the original typed reduction. -/
abbrev Normal {q : SimplexCategoryᵒᵖ} {s t : Objects C B x b}
    (p : Path C B x b q s t) : Prop :=
  DaggerNormalFormQuotient.Normal (Red C B x b q s t) p

/-- No original factor-identity letter, with its color and endpoints retained. -/
def IdentityFree (q : SimplexCategoryᵒᵖ) (l : List (Edge C B q)) : Prop :=
  ∀ e ∈ l, ¬ IsIdentity C B q e

/-- Adjacent actual tags differ; reversal of the snoc encoding does not change this condition. -/
def Alternating {q : SimplexCategoryᵒᵖ} : List (Edge C B q) → Prop
  | [] => True
  | [_] => True
  | e :: d :: l => e.1 ≠ d.1 ∧ Alternating (d :: l)

/-- A merge never erases a color merely because ambient endpoints coincide. -/
theorem merge_same_tag {q : SimplexCategoryᵒᵖ} {e d f : Edge C B q}
    (h : Merge C B q e d f) : e.1 = d.1 := by
  cases h
  rfl

/-- Actual composable same-color edges merge in their ORIGINAL factor category. -/
theorem merge_of_same_tag {q : SimplexCategoryᵒᵖ} {s t v : Objects C B x b}
    (h : (graphHom C B x b s t).obj q) (k : (graphHom C B x b t v).obj q)
    (hc : h.val.1 = k.val.1) : ∃ f, Merge C B q h.val k.val f := by
  rcases h with ⟨⟨c, a, d, h⟩, hs, ht⟩
  rcases k with ⟨⟨c', a', d', k⟩, ks, kt⟩
  change c = c' at hc
  cases hc
  have he : d = a' := label_injective C B x b c (ht.trans ks.symm)
  cases he
  exact ⟨tag C B q c (h ≫ k), Merge.intro c h k⟩

/-- Identity testing on an actual original loop is exactly equality to its degree identity. -/
theorem isIdentity_loop_iff (q : SimplexCategoryᵒᵖ) (c : Bool)
    (a : At C B q c) (h : a ⟶ a) :
    IsIdentity C B q (tag C B q c h) ↔ h = 𝟙 a := by
  constructor
  · intro hi
    cases hi
    rfl
  · rintro rfl
    exact IsIdentity.intro c a

/-- Every encoded one-step target is liftable with the SAME original path endpoints. -/
theorem normal_iff_encoded {q : SimplexCategoryᵒᵖ} {s t : Objects C B x b}
    (p : Path C B x b q s t) :
    Normal C B x b p ↔ ∀ l, ¬ ReverseEncodedRed C B q (encode C B x b p) l := by
  constructor
  · intro hn l hl
    obtain ⟨p', hp', _⟩ := lift_encoded C B x b hl p rfl
    exact hn p' hp'
  · intro hn p' hp'
    exact hn (encode C B x b p') ((red_iff_encoded C B x b).1 hp')

/-- A normal full path has a normal prefix, retaining the actual last-edge endpoints. -/
theorem normal_prefix {q : SimplexCategoryᵒᵖ} {s t v : Objects C B x b}
    {p : Path C B x b q s t} {e : (graphHom C B x b t v).obj q}
    (hn : Normal C B x b (p.cons e)) : Normal C B x b p := by
  intro p' hp'
  exact hn (p'.cons e) (red_cons C B x b hp' e)

/-- In particular the actual last tagged edge cannot be a factor identity. -/
theorem normal_last_not_identity {q : SimplexCategoryᵒᵖ} {s t v : Objects C B x b}
    {p : Path C B x b q s t} {e : (graphHom C B x b t v).obj q}
    (hn : Normal C B x b (p.cons e)) : ¬ IsIdentity C B q e.val := by
  intro hi
  exact (normal_iff_encoded C B x b (p.cons e)).1 hn (encode C B x b p)
    (ListRed.delete e.val _ hi)

/-- Both adjacent arrows retain different original tags, even when endpoints equal the glue. -/
theorem normal_last_tags {q : SimplexCategoryᵒᵖ} {s t v w : Objects C B x b}
    {p : Path C B x b q s t} {e : (graphHom C B x b t v).obj q}
    {d : (graphHom C B x b v w).obj q}
    (hn : Normal C B x b ((p.cons e).cons d)) : d.val.1 ≠ e.val.1 := by
  intro he
  obtain ⟨f, hm⟩ := merge_of_same_tag C B x b e d he.symm
  exact (normal_iff_encoded C B x b ((p.cons e).cons d)).1 hn
    (f :: encode C B x b p) (ListRed.merge d.val e.val f _ hm)

/-- All original identity letters, not just the endpoints, are excluded. -/
theorem normal_identityFree {q : SimplexCategoryᵒᵖ} {s t : Objects C B x b}
    {p : Path C B x b q s t} (hn : Normal C B x b p) :
    IdentityFree C B q (encode C B x b p) := by
  induction p with
  | nil => simp [IdentityFree, encode]
  | cons p e ih =>
    intro d hd
    rcases List.mem_cons.mp hd with rfl | hd
    · exact normal_last_not_identity C B x b hn
    · exact ih (normal_prefix C B x b hn) d hd

/-- Alternation is on the full encoded original path, with no subsingleton-Hom premise. -/
theorem normal_alternating {q : SimplexCategoryᵒᵖ} {s t : Objects C B x b}
    {p : Path C B x b q s t} (hn : Normal C B x b p) :
    Alternating C B (encode C B x b p) := by
  induction p with
  | nil => trivial
  | cons p e ih =>
    cases p with
    | nil => trivial
    | cons p d =>
      exact ⟨normal_last_tags C B x b hn, ih (normal_prefix C B x b hn)⟩

private theorem alternating_tail {q : SimplexCategoryᵒᵖ}
    (e : Edge C B q) (l : List (Edge C B q)) :
    Alternating C B (e :: l) → Alternating C B l := by
  cases l with
  | nil => exact fun _ ↦ trivial
  | cons d l => exact And.right

/-- The original list relation has no step on any identity-free alternating tagged list. -/
theorem no_encoded_step {q : SimplexCategoryᵒᵖ} {l l' : List (Edge C B q)}
    (hi : IdentityFree C B q l) (ha : Alternating C B l) :
    ¬ ReverseEncodedRed C B q l l' := by
  intro hr
  induction hr with
  | delete e l he => exact hi e (List.mem_cons_self ..) he
  | merge e d f l hm => exact ha.1 (merge_same_tag C B hm).symm
  | cons e hr ih =>
    apply ih
    · exact fun d hd ↦ hi d (List.mem_cons_of_mem e hd)
    · exact alternating_tail C B e _ ha

/-- Complete characterization on the SAME original dependent paths and reduction. -/
theorem normal_iff {q : SimplexCategoryᵒᵖ} {s t : Objects C B x b}
    (p : Path C B x b q s t) :
    Normal C B x b p ↔
      IdentityFree C B q (encode C B x b p) ∧ Alternating C B (encode C B x b p) := by
  constructor
  · intro hn
    exact ⟨normal_identityFree C B x b hn, normal_alternating C B x b hn⟩
  · rintro ⟨hi, ha⟩
    exact (normal_iff_encoded C B x b p).2 (fun _ ↦ no_encoded_step C B hi ha)

/-- Actual nil is normal at every original object and every degree. -/
theorem normal_nil (q : SimplexCategoryᵒᵖ) (s : Objects C B x b) :
    Normal C B x b (.nil : Path C B x b q s s) := by
  rw [normal_iff]
  exact ⟨by simp [IdentityFree, encode], trivial⟩

/-- A full original singleton is normal exactly when its tagged arrow is not an identity. -/
theorem normal_factorPath_iff {q : SimplexCategoryᵒᵖ} (c : Bool)
    {a d : At C B q c} (h : a ⟶ d) :
    Normal C B x b (factorPath C B x b c q h) ↔
      ¬ IsIdentity C B q (tag C B q c h) := by
  rw [normal_iff]
  simp [IdentityFree, Alternating]

/-- Exact last-edge criterion, retaining the full original prefix and reverse encoding. -/
theorem normal_cons_iff {q : SimplexCategoryᵒᵖ} {s t v : Objects C B x b}
    (p : Path C B x b q s t) (e : (graphHom C B x b t v).obj q) :
    Normal C B x b (p.cons e) ↔ Normal C B x b p ∧ ¬ IsIdentity C B q e.val ∧
      ∀ d l, encode C B x b p = d :: l → e.val.1 ≠ d.1 := by
  constructor
  · intro hn
    refine ⟨normal_prefix C B x b hn, normal_last_not_identity C B x b hn, ?_⟩
    intro d l he
    cases p with
    | nil => cases he
    | cons p f =>
      have hd := (List.cons.inj he).1
      rw [← hd]
      exact normal_last_tags C B x b hn
  · rintro ⟨hn, hi, ht⟩
    apply (normal_iff C B x b _).2
    refine ⟨?_, ?_⟩
    · intro d hd
      rcases List.mem_cons.mp hd with rfl | hd
      · exact hi
      · exact normal_identityFree C B x b hn d hd
    · cases p with
      | nil => trivial
      | cons p f =>
        exact ⟨ht f.val (encode C B x b p) rfl, normal_alternating C B x b hn⟩

/-- Normality is preserved in BOTH directions by literal original endpoint transport. -/
theorem normal_castPath_iff {q : SimplexCategoryᵒᵖ}
    {s t s' t' : Objects C B x b} (hs : s = s') (ht : t = t')
    (p : Path C B x b q s t) :
    Normal C B x b (castPath C B x b hs ht p) ↔ Normal C B x b p := by
  cases hs
  cases ht
  rfl

end
end DaggerAmalgamPaddedClassification
