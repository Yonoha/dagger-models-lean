import AmalgamPaddedOccurrences

/-! Original contextual unit deletion and neighbor composition, with full typed face data. -/

open CategoryTheory DaggerModels DaggerAmalgamPresentation DaggerAmalgamReduction
open DaggerAmalgamPaddedClassification DaggerAmalgamNormalForms DaggerAmalgamPathMeasure

universe u
namespace DaggerAmalgamPaddedClassifier
noncomputable section
set_option autoImplicit false
variable (C B : SimplicialCat.{u, u}) (x : C.Obj) (b : B.Obj)

theorem alternating_suffix {q : SimplexCategoryᵒᵖ} (pre l : List (Edge C B q))
    (ha : Alternating C B (pre ++ l)) : Alternating C B l := by
  induction pre with
  | nil => exact ha
  | cons d pre ih =>
    apply ih
    cases h : pre ++ l with
    | nil => trivial
    | cons e tail => exact (show Alternating C B (d :: e :: tail) from h ▸ ha).2

/-- Composability is taken from the SAME dependent path, never from color equality alone. -/
theorem merge_at_encoded_adjacency {q : SimplexCategoryᵒᵖ}
    (pre : List (Edge C B q)) (e f : Edge C B q) (post : List (Edge C B q))
    {s t : Objects C B x b} (p : Path C B x b q s t)
    (he : encode C B x b p = pre ++ e :: f :: post) (hc : e.1 = f.1) :
    ∃ g, Merge C B q f e g := by
  induction pre generalizing s t with
  | nil =>
    cases p with
    | nil => cases he
    | cons p last =>
      cases p with
      | nil => cases he
      | cons p prev =>
        have h := List.cons.inj he
        have h' := List.cons.inj h.2
        have hl : last.val = e := h.1
        have hp : prev.val = f := h'.1
        obtain ⟨g, hg⟩ := merge_of_same_tag C B x b prev last
          (by rw [hp, hl]; exact hc.symm)
        exact ⟨g, by simpa only [hp, hl] using hg⟩
  | cons d pre ih =>
    cases p with
    | nil => cases he
    | cons p last => exact ih p (List.cons.inj he).2

/-- Every chosen coordinate face retains both literal original reduction steps and all maps. -/
structure UnitFaceData {q : SimplexCategoryᵒᵖ} {s t : Objects C B x b}
    (p : Path C B x b q s t) (unit : Edge C B q) where
  pre : List (Edge C B q)
  left : Edge C B q
  right : Edge C B q
  post : List (Edge C B q)
  composed : Edge C B q
  afterDelete : Path C B x b q s t
  face : Path C B x b q s t
  original_encode : encode C B x b p = pre ++ left :: unit :: right :: post
  unit_identity : IsIdentity C B q unit
  neighbors_composition : Merge C B q right left composed
  delete_step : Red C B x b q s t p afterDelete
  deleted_encode : encode C B x b afterDelete = pre ++ left :: right :: post
  merge_step : Red C B x b q s t afterDelete face
  face_encode : encode C B x b face = pre ++ composed :: post
  count_drop : rightCount C B x b q face + 1 = rightCount C B x b q p
  same_normal : normalize C B x b p = normalize C B x b face

theorem exists_unitFace {q : SimplexCategoryᵒᵖ} {s t : Objects C B x b}
    (p : Path C B x b q s t) (unit : Edge C B q)
    (ha : Alternating C B (encode C B x b p)) (hi : IsIdentity C B q unit)
    (ho : InnerOccurrence C B unit (encode C B x b p)) :
    Nonempty (UnitFaceData C B x b p unit) := by
  rcases ho with ⟨pre, left, right, post, he⟩
  have hal : Alternating C B (left :: unit :: right :: post) :=
    alternating_suffix C B pre _ (he ▸ ha)
  have hc : left.1 = right.1 := by
    have hl := hal.1
    have hr := hal.2.1
    cases hleft : left.1 <;> cases hunit : unit.1 <;> cases hright : right.1 <;>
      simp_all
  have hd : ReverseEncodedRed C B q (pre ++ left :: unit :: right :: post)
      (pre ++ left :: right :: post) :=
    listRed_append_left pre (.cons left (.delete unit (right :: post) hi))
  obtain ⟨pd, hpd, hed⟩ := lift_encoded C B x b hd p he
  obtain ⟨composed, hm⟩ := merge_at_encoded_adjacency C B x b pre left right post pd hed hc
  have hm' : ReverseEncodedRed C B q (pre ++ left :: right :: post)
      (pre ++ composed :: post) := listRed_append_left pre (.merge left right composed post hm)
  obtain ⟨pf, hpf, hef⟩ := lift_encoded C B x b hm' pd hed
  have hcount : rightCount C B x b q pf + 1 = rightCount C B x b q p := by
    rw [← bCount_encode, ← bCount_encode, hef, he, bCount_append, bCount_append]
    have hne := hal.1
    cases hm with
    | @intro c a d v h k =>
      cases hi with
      | intro cu obj =>
        cases c <;> cases cu <;> simp [bCount, tag] at hne ⊢ <;> omega
  exact ⟨⟨pre, left, right, post, composed, pd, pf, he, hi, hm, hpd, hed, hpf, hef,
    hcount, (normalize_finite C B x b (.single hpd)).trans
      (normalize_finite C B x b (.single hpf))⟩⟩

/-- The chosen face is selected from the full original-data existence result. -/
def unitFace {q : SimplexCategoryᵒᵖ} {s t : Objects C B x b}
    (p : Path C B x b q s t) (unit : Edge C B q)
    (ha : Alternating C B (encode C B x b p)) (hi : IsIdentity C B q unit)
    (ho : InnerOccurrence C B unit (encode C B x b p)) :
    UnitFaceData C B x b p unit := Classical.choice (exists_unitFace C B x b p unit ha hi ho)

theorem UnitFaceData.normal_count_lt {q : SimplexCategoryᵒᵖ} {s t : Objects C B x b}
    {p : Path C B x b q s t} {unit : Edge C B q} (d : UnitFaceData C B x b p unit) :
    rightCount C B x b q (normalize C B x b p).val < rightCount C B x b q p := by
  rw [d.same_normal]
  have hle := count_normalize_le C B x b d.face
  have hc := d.count_drop
  omega

theorem UnitFaceData.same_quotient {q : SimplexCategoryᵒᵖ} {s t : Objects C B x b}
    {p : Path C B x b q s t} {unit : Edge C B q} (d : UnitFaceData C B x b p unit) :
    SimplicialCat.HomQuotient.mk (relations C B x b) q p =
      SimplicialCat.HomQuotient.mk (relations C B x b) q d.face := by
  rw [← mk_normalize C B x b p, d.same_normal, mk_normalize]

end
end DaggerAmalgamPaddedClassifier
