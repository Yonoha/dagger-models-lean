import AmalgamPaddedOperators

/-! Primitive faces are literal lower raw tuples, before any cascading normalization. -/

open CategoryTheory DaggerModels DaggerAmalgamPresentation DaggerAmalgamReduction
open DaggerAmalgamPaddedClassification DaggerAmalgamNormalForms DaggerAmalgamPathMeasure

universe u
namespace DaggerAmalgamPaddedClassifier
noncomputable section
set_option autoImplicit false
variable (C B : SimplicialCat.{u, u}) (x : C.Obj) (b : B.Obj)

theorem merge_color_left {q : SimplexCategoryᵒᵖ} {e f g : Edge C B q}
    (h : Merge C B q e f g) : g.1 = e.1 := by cases h; rfl

theorem merge_color_right {q : SimplexCategoryᵒᵖ} {e f g : Edge C B q}
    (h : Merge C B q e f g) : g.1 = f.1 := by cases h; rfl

theorem firstColor_append_nonempty {q : SimplexCategoryᵒᵖ}
    (pre : List (Edge C B q)) (e : Edge C B q) (post : List (Edge C B q)) :
    firstColor C B (pre ++ e :: post) = firstColor C B (e :: post) := by
  induction pre with
  | nil => rfl
  | cons d pre ih =>
    cases pre with
    | nil => cases post <;> rfl
    | cons f pre => exact ih

theorem alternating_replace_inner {q : SimplexCategoryᵒᵖ}
    (pre : List (Edge C B q)) (l e r g : Edge C B q) (post : List (Edge C B q))
    (hl : g.1 = l.1) (hr : g.1 = r.1)
    (ha : Alternating C B (pre ++ l :: e :: r :: post)) :
    Alternating C B (pre ++ g :: post) := by
  induction pre with
  | nil =>
    cases post with
    | nil => trivial
    | cons d post => exact ⟨hr ▸ ha.2.2.1, ha.2.2.2⟩
  | cons d pre ih =>
    cases pre with
    | nil =>
      refine ⟨?_, ih ha.2⟩
      exact hl ▸ ha.1
    | cons f pre => exact ⟨ha.1, ih ha.2⟩

theorem UnitFaceData.alternating {q : SimplexCategoryᵒᵖ} {s t : Objects C B x b}
    {p : Path C B x b q s t} {unit : Edge C B q} (d : UnitFaceData C B x b p unit)
    (ha : Alternating C B (encode C B x b p)) :
    Alternating C B (encode C B x b d.face) := by
  rw [d.face_encode]
  exact alternating_replace_inner C B d.pre d.left unit d.right d.composed d.post
    (merge_color_right C B d.neighbors_composition)
    (merge_color_left C B d.neighbors_composition) (d.original_encode ▸ ha)

theorem UnitFaceData.starts {q : SimplexCategoryᵒᵖ} {s t : Objects C B x b}
    {p : Path C B x b q s t} {unit : Edge C B q} (d : UnitFaceData C B x b p unit)
    (c : Bool) (hs : Starts C B x b p c) : Starts C B x b d.face c := by
  unfold Starts at hs ⊢
  rw [d.original_encode, firstColor_append_nonempty] at hs
  rw [d.face_encode, firstColor_append_nonempty]
  have hc := merge_color_left C B d.neighbors_composition
  cases hp : d.post with
  | nil => simpa only [hp, firstColor, hc] using hs
  | cons e post => simpa only [hp, firstColor] using hs

theorem UnitFaceData.ends {q : SimplexCategoryᵒᵖ} {s t : Objects C B x b}
    {p : Path C B x b q s t} {unit : Edge C B q} (d : UnitFaceData C B x b p unit)
    (c : Bool) (hs : Ends C B x b p c) : Ends C B x b d.face c := by
  unfold Ends at hs ⊢
  rw [d.original_encode] at hs
  rw [d.face_encode]
  have hc := merge_color_right C B d.neighbors_composition
  cases hp : d.pre with
  | nil => simpa only [hp, List.nil_append, List.head?_cons, Option.map_some, hc] using hs
  | cons e pre => simpa only [hp, List.cons_append, List.head?_cons, Option.map_some] using hs

theorem colors_decodeOO (q : SimplexCategoryᵒᵖ) (a d : C.Obj) (r : ℕ)
    (h : RawOO C B x b q a d r) :
    Starts C B x b (decodeOO C B x b q a d r h) false ∧
      Ends C B x b (decodeOO C B x b q a d r h) false := by
  cases r with
  | zero => exact ⟨rfl, rfl⟩
  | succ n =>
    simp only [Starts, Ends, decodeOO, encode_comp, encode_factorPath,
      encode_bLoop, List.cons_append, List.nil_append,
      List.head?_cons, Option.map_some]
    constructor
    · simp only [← List.cons_append, firstColor_append_singleton]
      rfl
    · rfl

theorem exists_rawFaceOO (q : SimplexCategoryᵒᵖ) (a d : C.Obj) (n : ℕ)
    (h : RawOO C B x b q a d (n + 1)) (unit : Edge C B q)
    (fd : UnitFaceData C B x b (decodeOO C B x b q a d (n + 1) h) unit) :
    ∃ k : RawOO C B x b q a d n, decodeOO C B x b q a d n k = fd.face := by
  obtain ⟨r, k, hk⟩ := exists_raw_path C B x b false false a d fd.face
    (fd.alternating C B x b (alternating_decodeOO C B x b q a d (n + 1) h))
    (fd.starts C B x b false (colors_decodeOO C B x b q a d (n + 1) h).1)
    (fd.ends C B x b false (colors_decodeOO C B x b q a d (n + 1) h).2)
  have he : decodeOO C B x b q a d r k = fd.face := hk
  have hc := fd.count_drop
  rw [← he, count_decodeOO, count_decodeOO] at hc
  have hr : r = n := by omega
  subst r
  exact ⟨k, he⟩

def rawFaceOO (q : SimplexCategoryᵒᵖ) (a d : C.Obj) (n : ℕ)
    (h : RawOO C B x b q a d (n + 1)) (unit : Edge C B q)
    (fd : UnitFaceData C B x b (decodeOO C B x b q a d (n + 1) h) unit) :
    RawOO C B x b q a d n := Classical.choose (exists_rawFaceOO C B x b q a d n h unit fd)

theorem rawFaceOO_decode (q : SimplexCategoryᵒᵖ) (a d : C.Obj) (n : ℕ)
    (h : RawOO C B x b q a d (n + 1)) (unit : Edge C B q)
    (fd : UnitFaceData C B x b (decodeOO C B x b q a d (n + 1) h) unit) :
    decodeOO C B x b q a d n (rawFaceOO C B x b q a d n h unit fd) = fd.face :=
  Classical.choose_spec (exists_rawFaceOO C B x b q a d n h unit fd)

theorem rawFaceOO_eval (q : SimplexCategoryᵒᵖ) (a d : C.Obj) (n : ℕ)
    (h : RawOO C B x b q a d (n + 1)) (unit : Edge C B q)
    (fd : UnitFaceData C B x b (decodeOO C B x b q a d (n + 1) h) unit) :
    evalOO C B x b q a d n (rawFaceOO C B x b q a d n h unit fd) =
      evalOO C B x b q a d (n + 1) h := by
  unfold evalOO
  rw [rawFaceOO_decode]
  exact (fd.same_quotient C B x b).symm

theorem colors_decodeON (q : SimplexCategoryᵒᵖ) (a : C.Obj) (w : B.Obj) (r : ℕ)
    (h : RawON C B x b q a w r) :
    Starts C B x b (decodeON C B x b q a w r h) false ∧
      Ends C B x b (decodeON C B x b q a w r h) true := by
  simp only [Starts, Ends, decodeON, encode_comp, encode_factorPath,
      encode_bEnd, List.cons_append, List.nil_append,
      List.head?_cons, Option.map_some]
  constructor
  · simp only [← List.cons_append, firstColor_append_singleton]
    rfl
  · rfl

theorem exists_rawFaceON (q : SimplexCategoryᵒᵖ) (a : C.Obj) (w : B.Obj) (n : ℕ)
    (h : RawON C B x b q a w (n + 1)) (unit : Edge C B q)
    (fd : UnitFaceData C B x b (decodeON C B x b q a w (n + 1) h) unit) :
    ∃ k : RawON C B x b q a w n, decodeON C B x b q a w n k = fd.face := by
  obtain ⟨r, k, hk⟩ := exists_raw_path C B x b false true a w fd.face
    (fd.alternating C B x b (alternating_decodeON C B x b q a w (n + 1) h))
    (fd.starts C B x b false (colors_decodeON C B x b q a w (n + 1) h).1)
    (fd.ends C B x b true (colors_decodeON C B x b q a w (n + 1) h).2)
  have he : decodeON C B x b q a w r k = fd.face := hk
  have hc := fd.count_drop
  rw [← he, count_decodeON, count_decodeON] at hc
  have hr : r = n := by omega
  subst r
  exact ⟨k, he⟩

def rawFaceON (q : SimplexCategoryᵒᵖ) (a : C.Obj) (w : B.Obj) (n : ℕ)
    (h : RawON C B x b q a w (n + 1)) (unit : Edge C B q)
    (fd : UnitFaceData C B x b (decodeON C B x b q a w (n + 1) h) unit) :
    RawON C B x b q a w n := Classical.choose (exists_rawFaceON C B x b q a w n h unit fd)

theorem rawFaceON_decode (q : SimplexCategoryᵒᵖ) (a : C.Obj) (w : B.Obj) (n : ℕ)
    (h : RawON C B x b q a w (n + 1)) (unit : Edge C B q)
    (fd : UnitFaceData C B x b (decodeON C B x b q a w (n + 1) h) unit) :
    decodeON C B x b q a w n (rawFaceON C B x b q a w n h unit fd) = fd.face :=
  Classical.choose_spec (exists_rawFaceON C B x b q a w n h unit fd)

theorem rawFaceON_eval (q : SimplexCategoryᵒᵖ) (a : C.Obj) (w : B.Obj) (n : ℕ)
    (h : RawON C B x b q a w (n + 1)) (unit : Edge C B q)
    (fd : UnitFaceData C B x b (decodeON C B x b q a w (n + 1) h) unit) :
    evalON C B x b q a w n (rawFaceON C B x b q a w n h unit fd) =
      evalON C B x b q a w (n + 1) h := by
  unfold evalON
  rw [rawFaceON_decode]
  exact (fd.same_quotient C B x b).symm

theorem colors_decodeNO (q : SimplexCategoryᵒᵖ) (z : B.Obj) (d : C.Obj) (r : ℕ)
    (h : RawNO C B x b q z d r) :
    Starts C B x b (decodeNO C B x b q z d r h) true ∧
      Ends C B x b (decodeNO C B x b q z d r h) false := by
  simp only [Starts, Ends, decodeNO, encode_comp, encode_factorPath,
      encode_bStart, List.cons_append, List.nil_append,
      List.head?_cons, Option.map_some]
  constructor
  · simp only [← List.cons_append, firstColor_append_singleton]
    rfl
  · rfl

theorem exists_rawFaceNO (q : SimplexCategoryᵒᵖ) (z : B.Obj) (d : C.Obj) (n : ℕ)
    (h : RawNO C B x b q z d (n + 1)) (unit : Edge C B q)
    (fd : UnitFaceData C B x b (decodeNO C B x b q z d (n + 1) h) unit) :
    ∃ k : RawNO C B x b q z d n, decodeNO C B x b q z d n k = fd.face := by
  obtain ⟨r, k, hk⟩ := exists_raw_path C B x b true false z d fd.face
    (fd.alternating C B x b (alternating_decodeNO C B x b q z d (n + 1) h))
    (fd.starts C B x b true (colors_decodeNO C B x b q z d (n + 1) h).1)
    (fd.ends C B x b false (colors_decodeNO C B x b q z d (n + 1) h).2)
  have he : decodeNO C B x b q z d r k = fd.face := hk
  have hc := fd.count_drop
  rw [← he, count_decodeNO, count_decodeNO] at hc
  have hr : r = n := by omega
  subst r
  exact ⟨k, he⟩

def rawFaceNO (q : SimplexCategoryᵒᵖ) (z : B.Obj) (d : C.Obj) (n : ℕ)
    (h : RawNO C B x b q z d (n + 1)) (unit : Edge C B q)
    (fd : UnitFaceData C B x b (decodeNO C B x b q z d (n + 1) h) unit) :
    RawNO C B x b q z d n := Classical.choose (exists_rawFaceNO C B x b q z d n h unit fd)

theorem rawFaceNO_decode (q : SimplexCategoryᵒᵖ) (z : B.Obj) (d : C.Obj) (n : ℕ)
    (h : RawNO C B x b q z d (n + 1)) (unit : Edge C B q)
    (fd : UnitFaceData C B x b (decodeNO C B x b q z d (n + 1) h) unit) :
    decodeNO C B x b q z d n (rawFaceNO C B x b q z d n h unit fd) = fd.face :=
  Classical.choose_spec (exists_rawFaceNO C B x b q z d n h unit fd)

theorem rawFaceNO_eval (q : SimplexCategoryᵒᵖ) (z : B.Obj) (d : C.Obj) (n : ℕ)
    (h : RawNO C B x b q z d (n + 1)) (unit : Edge C B q)
    (fd : UnitFaceData C B x b (decodeNO C B x b q z d (n + 1) h) unit) :
    evalNO C B x b q z d n (rawFaceNO C B x b q z d n h unit fd) =
      evalNO C B x b q z d (n + 1) h := by
  unfold evalNO
  rw [rawFaceNO_decode]
  exact (fd.same_quotient C B x b).symm

theorem colors_decodeNN (q : SimplexCategoryᵒᵖ) (z w : B.Obj) (r : ℕ)
    (h : RawNN C B x b q z w r) :
    Starts C B x b (decodeNN C B x b q z w r h) true ∧
      Ends C B x b (decodeNN C B x b q z w r h) true := by
  cases r with
  | zero => exact ⟨rfl, rfl⟩
  | succ n =>
    simp only [Starts, Ends, decodeNN, encode_comp, encode_factorPath,
      encode_bStart, encode_bEnd, List.cons_append, List.nil_append,
      List.head?_cons, Option.map_some]
    constructor
    · simp only [← List.cons_append, firstColor_append_singleton]
      rfl
    · rfl

theorem exists_rawFaceNN (q : SimplexCategoryᵒᵖ) (z w : B.Obj) (n : ℕ)
    (h : RawNN C B x b q z w (n + 1)) (unit : Edge C B q)
    (fd : UnitFaceData C B x b (decodeNN C B x b q z w (n + 1) h) unit) :
    ∃ k : RawNN C B x b q z w n, decodeNN C B x b q z w n k = fd.face := by
  obtain ⟨r, k, hk⟩ := exists_raw_path C B x b true true z w fd.face
    (fd.alternating C B x b (alternating_decodeNN C B x b q z w (n + 1) h))
    (fd.starts C B x b true (colors_decodeNN C B x b q z w (n + 1) h).1)
    (fd.ends C B x b true (colors_decodeNN C B x b q z w (n + 1) h).2)
  have he : decodeNN C B x b q z w r k = fd.face := hk
  have hc := fd.count_drop
  rw [← he, count_decodeNN, count_decodeNN] at hc
  have hr : r = n := by omega
  subst r
  exact ⟨k, he⟩

def rawFaceNN (q : SimplexCategoryᵒᵖ) (z w : B.Obj) (n : ℕ)
    (h : RawNN C B x b q z w (n + 1)) (unit : Edge C B q)
    (fd : UnitFaceData C B x b (decodeNN C B x b q z w (n + 1) h) unit) :
    RawNN C B x b q z w n := Classical.choose (exists_rawFaceNN C B x b q z w n h unit fd)

theorem rawFaceNN_decode (q : SimplexCategoryᵒᵖ) (z w : B.Obj) (n : ℕ)
    (h : RawNN C B x b q z w (n + 1)) (unit : Edge C B q)
    (fd : UnitFaceData C B x b (decodeNN C B x b q z w (n + 1) h) unit) :
    decodeNN C B x b q z w n (rawFaceNN C B x b q z w n h unit fd) = fd.face :=
  Classical.choose_spec (exists_rawFaceNN C B x b q z w n h unit fd)

theorem rawFaceNN_eval (q : SimplexCategoryᵒᵖ) (z w : B.Obj) (n : ℕ)
    (h : RawNN C B x b q z w (n + 1)) (unit : Edge C B q)
    (fd : UnitFaceData C B x b (decodeNN C B x b q z w (n + 1) h) unit) :
    evalNN C B x b q z w n (rawFaceNN C B x b q z w n h unit fd) =
      evalNN C B x b q z w (n + 1) h := by
  unfold evalNN
  rw [rawFaceNN_decode]
  exact (fd.same_quotient C B x b).symm

end
end DaggerAmalgamPaddedClassifier
