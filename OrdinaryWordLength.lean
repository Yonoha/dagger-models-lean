import OrdinaryCellNormalizer

/-! Length of the actual original contextual normal forms and their original word boundary.
The original Q and wordEvaluation are retained; simplex operators can enter A and reduce length. -/

open CategoryTheory DaggerModels
open scoped Classical
open DaggerRelativeOneCellPresentation DaggerOrdinaryReducedWords DaggerOrdinaryWordBoundary
open DaggerOrdinaryCellNormalizer

universe u

namespace DaggerOrdinaryWordLength

noncomputable section

variable (C : SimplicialCat.{u, u}) (x y : C.Obj) {L : SSet.{u}}
variable (A : L.Subcomplex) (uA : (A : SSet.{u}) ⟶ (x ⟶[SSet] y))

/-- Count exactly the original L letters outside A, at the given degree. -/
def outsideCount (q : SimplexCategoryᵒᵖ) : (n : ℕ) → (a b : C.Obj) →
    (Word C x y L n a b).obj q → ℕ := by
  classical
  exact fun n ↦ match n with
    | 0 => fun _ _ _ ↦ 0
    | n + 1 => fun _ b w ↦ (if w.1.2 ∈ A.obj q then 0 else 1) +
        outsideCount q n y b w.2

theorem outsideCount_le (q : SimplexCategoryᵒᵖ) (n : ℕ) (a b : C.Obj)
    (w : (Word C x y L n a b).obj q) : outsideCount C x y A q n a b w ≤ n := by
  classical
  induction n generalizing a with
  | zero => exact Nat.le_refl 0
  | succ n ih =>
    change (if w.1.2 ∈ A.obj q then 0 else 1) + outsideCount C x y A q n y b w.2 ≤ n + 1
    have ht := ih y w.2
    split_ifs <;> omega

theorem outsideCount_lt_iff_boundary (q : SimplexCategoryᵒᵖ) (n : ℕ) (a b : C.Obj)
    (w : (Word C x y L n a b).obj q) :
    outsideCount C x y A q n a b w < n ↔ w ∈ (Boundary C x y A n a b).obj q := by
  classical
  induction n generalizing a with
  | zero => exact iff_of_false (Nat.not_lt_zero 0) (fun h ↦ h)
  | succ n ih =>
    rw [mem_boundary_succ]
    change (if w.1.2 ∈ A.obj q then 0 else 1) + outsideCount C x y A q n y b w.2 < n + 1 ↔ _
    have ht := outsideCount_le C x y A q n y b w.2
    by_cases hl : w.1.2 ∈ A.obj q
    · rw [if_pos hl]
      exact iff_of_true (by omega) (Or.inl hl)
    · simp only [hl, if_false, false_or]
      rw [← ih y w.2]
      omega

theorem newAction_length (q : SimplexCategoryᵒᵖ) {a : C.Obj}
    (w : Reduced C x y A q a x) (l : L.obj q) :
    (newAction C x y A uA q w l).1 = w.1 + (if l ∈ A.obj q then 0 else 1) := by
  classical
  by_cases hl : l ∈ A.obj q
  · simp only [newAction, dif_pos hl, if_pos hl]
    rfl
  · simp only [newAction, dif_neg hl, if_neg hl]
    rfl

/-- Exact length for the original decoded raw word, in every arbitrary reduced prefix. -/
theorem act_decodeWord_length (q : SimplexCategoryᵒᵖ) (n : ℕ) {a : C.Obj} (b c : C.Obj)
    (w : (Word C x y L n b c).obj q) (p : Reduced C x y A q a b) :
    (act C x y A uA q p (decodeWord C x y q n b c w)).1 =
      p.1 + outsideCount C x y A q n b c w := by
  classical
  induction n generalizing b with
  | zero => rfl
  | succ n ih =>
    change (act C x y A uA q p ((oldPath C x y q w.1.1).comp
      ((newPath C x y q w.1.2).comp (decodeWord C x y q n y c w.2)))).1 = _
    rw [act_comp, act_comp, act_oldPath, act_newPath, ih, newAction_length]
    exact Nat.add_assoc p.1 (if w.1.2 ∈ A.obj q then 0 else 1)
      (outsideCount C x y A q n y c w.2)

theorem normalize_word_length (q : SimplexCategoryᵒᵖ) (n : ℕ) (a b : C.Obj)
    (w : (Word C x y L n a b).obj q) :
    (normalize C x y A uA q a b ((wordEvaluation C x y A uA n a b).app q w)).1 =
      outsideCount C x y A q n a b w := by
  simpa only [initial, old, Nat.zero_add] using
    act_decodeWord_length C x y A uA q n a b w (initial C x y A q a)

theorem normalize_word_length_le (q : SimplexCategoryᵒᵖ) (n : ℕ) (a b : C.Obj)
    (w : (Word C x y L n a b).obj q) :
    (normalize C x y A uA q a b ((wordEvaluation C x y A uA n a b).app q w)).1 ≤ n := by
  rw [normalize_word_length]
  exact outsideCount_le C x y A q n a b w

theorem normalize_word_length_lt_iff_boundary (q : SimplexCategoryᵒᵖ)
    (n : ℕ) (a b : C.Obj) (w : (Word C x y L n a b).obj q) :
    (normalize C x y A uA q a b ((wordEvaluation C x y A uA n a b).app q w)).1 < n ↔
      w ∈ (Boundary C x y A n a b).obj q := by
  rw [normalize_word_length]
  exact outsideCount_lt_iff_boundary C x y A q n a b w

/-- Outside the original boundary the complete original reduced form, not only length, is exact. -/
theorem normalize_word_outside_boundary (q : SimplexCategoryᵒᵖ)
    (n : ℕ) (a b : C.Obj) (w : (Word C x y L n a b).obj q)
    (hw : w ∉ (Boundary C x y A n a b).obj q) :
    normalize C x y A uA q a b ((wordEvaluation C x y A uA n a b).app q w) = ⟨n, w, hw⟩ :=
  normalize_decodeWord C x y A uA q n a b w hw

/-- Every actual Q simplex operator renormalizes to a word of no greater length. -/
theorem normalize_map_length_le {q q' : SimplexCategoryᵒᵖ} (α : q ⟶ q') (a b : C.Obj)
    (z : SimplicialCat.HomQuotient.HomObj (relations C x y A.ι uA) q a b) :
    (normalize C x y A uA q' a b
      ((SimplicialCat.HomQuotient.hom (relations C x y A.ι uA) a b).map α z)).1 ≤
        (normalize C x y A uA q a b z).1 := by
  let w := normalize C x y A uA q a b z
  have hz : (wordEvaluation C x y A uA w.1 a b).app q w.2.val = z :=
    decodeClass_normalize C x y A uA q a b z
  rw [← hz]
  have hn := congrFun ((wordEvaluation C x y A uA w.1 a b).naturality α) w.2.val
  change (wordEvaluation C x y A uA w.1 a b).app q'
    ((Word C x y L w.1 a b).map α w.2.val) =
      (SimplicialCat.HomQuotient.hom (relations C x y A.ι uA) a b).map α
        ((wordEvaluation C x y A uA w.1 a b).app q w.2.val) at hn
  rw [← hn]
  change (normalize C x y A uA q' a b _).1 ≤ _
  rw [normalize_word_outside_boundary C x y A uA q w.1 a b w.2.val w.2.property]
  exact normalize_word_length_le C x y A uA q' w.1 a b
      ((Word C x y L w.1 a b).map α w.2.val)


/-- Actual length-bounded subcomplex of the same original Q Hom. -/
def stage (n : ℕ) (a b : C.Obj) :
    (SimplicialCat.HomQuotient.hom (relations C x y A.ι uA) a b).Subcomplex where
  obj q := {z | (normalize C x y A uA q a b z).1 ≤ n}
  map α z hz := (normalize_map_length_le C x y A uA α a b z).trans hz

@[simp] theorem mem_stage (n : ℕ) (a b : C.Obj) (q : SimplexCategoryᵒᵖ)
    (z : SimplicialCat.HomQuotient.HomObj (relations C x y A.ι uA) q a b) :
    z ∈ (stage C x y A uA n a b).obj q ↔ (normalize C x y A uA q a b z).1 ≤ n := Iff.rfl

/-- The same positive word evaluates in the previous stage exactly on its original boundary. -/
theorem wordEvaluation_mem_previous_stage_iff_boundary (q : SimplexCategoryᵒᵖ)
    (n : ℕ) (a b : C.Obj) (w : (Word C x y L (n + 1) a b).obj q) :
    (wordEvaluation C x y A uA (n + 1) a b).app q w ∈
      (stage C x y A uA n a b).obj q ↔ w ∈ (Boundary C x y A (n + 1) a b).obj q := by
  rw [mem_stage, ← Nat.lt_succ_iff]
  exact normalize_word_length_lt_iff_boundary C x y A uA q (n + 1) a b w

theorem stage_monotone (a b : C.Obj) : Monotone (fun n ↦ stage C x y A uA n a b) :=
  fun _ _ h _ _ hz ↦ hz.trans h

theorem wordEvaluation_range_le (n : ℕ) (a b : C.Obj) :
    SSet.Subcomplex.range (wordEvaluation C x y A uA n a b) ≤ stage C x y A uA n a b := by
  intro q z hz
  rcases hz with ⟨w, rfl⟩
  exact normalize_word_length_le C x y A uA q n a b w

/-- The very same wordEvaluation, factored through its actual length stage. -/
def wordToStage (n : ℕ) (a b : C.Obj) :
    Word C x y L n a b ⟶ (stage C x y A uA n a b : SSet.{u}) :=
  SSet.Subcomplex.lift (wordEvaluation C x y A uA n a b)
    (wordEvaluation_range_le C x y A uA n a b)

@[reassoc] theorem wordToStage_ι (n : ℕ) (a b : C.Obj) :
    wordToStage C x y A uA n a b ≫ (stage C x y A uA n a b).ι =
      wordEvaluation C x y A uA n a b := rfl

/-- Stage zero is exactly the actual range of the original old Hom map. -/
theorem stage_zero_eq_range (a b : C.Obj) :
    stage C x y A uA 0 a b = SSet.Subcomplex.range ((v C x y A.ι uA).map a b) := by
  ext q z
  change (normalize C x y A uA q a b z).1 ≤ 0 ↔
    ∃ h, ((v C x y A.ι uA).map a b).app q h = z
  constructor
  · intro hz
    generalize hred : normalize C x y A uA q a b z = red at hz
    rcases red with ⟨n, w⟩
    have hn : n = 0 := Nat.eq_zero_of_le_zero hz
    subst n
    have hd := decodeClass_normalize C x y A uA q a b z
    rw [hred] at hd
    exact ⟨w.val, hd⟩
  · rintro ⟨h, rfl⟩
    rw [normalize_oldMap]
    exact Nat.le_refl 0

/-- Full simplicial isomorphism with the original old Hom, using its proved Mono. -/
def stageZeroIso (a b : C.Obj) :
    (a ⟶[SSet] b) ≅ (stage C x y A uA 0 a b : SSet.{u}) :=
  asIso (SSet.Subcomplex.toRange ((v C x y A.ι uA).map a b)) ≪≫
    SSet.Subcomplex.eqToIso (stage_zero_eq_range C x y A uA a b).symm

@[reassoc] theorem stageZeroIso_hom_ι (a b : C.Obj) :
    (stageZeroIso C x y A uA a b).hom ≫ (stage C x y A uA 0 a b).ι =
      (v C x y A.ι uA).map a b := by
  simp only [stageZeroIso, Iso.trans_hom, asIso_hom, Category.assoc,
    SSet.Subcomplex.eqToIso, SSet.Subcomplex.homOfLE_ι, SSet.Subcomplex.toRange_ι]

end

end DaggerOrdinaryWordLength
