import AmalgamPaddedRankDrop
import AmalgamRank

/-! Evaluation into the SAME quotient and actual rank subcomplex: full boundary and interiors. -/

open CategoryTheory DaggerModels DaggerAmalgamPresentation
open DaggerAmalgamPaddedClassification DaggerAmalgamNormalForms DaggerAmalgamPathMeasure
open DaggerAmalgamRankFiltration

universe u
namespace DaggerAmalgamPaddedClassifier
noncomputable section
set_option autoImplicit false
variable (C B : SimplicialCat.{u, u}) (x : C.Obj) (b : B.Obj)

def evalOO (q : SimplexCategoryᵒᵖ) (a d : C.Obj) (r : ℕ)
    (h : RawOO C B x b q a d r) :
    SimplicialCat.HomQuotient.HomObj (relations C B x b) q (leftObj C B x b a) (leftObj C B x b
        d) :=
  SimplicialCat.HomQuotient.mk _ q (decodeOO C B x b q a d r h)

theorem rank_evalOO (q : SimplexCategoryᵒᵖ) (a d : C.Obj) (r : ℕ)
    (h : RawOO C B x b q a d r) :
    rankOf C B x b false q (evalOO C B x b q a d r h) =
      rightCount C B x b q (normalize C B x b (decodeOO C B x b q a d r h)).val := by
  simp [evalOO, rankOf, rank, homEquiv_mk]

theorem evalOO_mem_stage (q : SimplexCategoryᵒᵖ) (a d : C.Obj) (r : ℕ)
    (h : RawOO C B x b q a d r) :
    evalOO C B x b q a d r h ∈ (stage C B x b false r (leftObj C B x b a) (leftObj C B x b
        d)).obj q := by
  rw [mem_stage, rank_evalOO]
  exact rank_decodeOO_le C B x b q a d r h

theorem evalOO_mem_previous_iff (q : SimplexCategoryᵒᵖ) (a d : C.Obj) (n : ℕ)
    (h : RawOO C B x b q a d (n + 1)) :
    evalOO C B x b q a d (n + 1) h ∈
        (stage C B x b false n (leftObj C B x b a) (leftObj C B x b d)).obj q ↔
      criticalOO C B x b q a d (n + 1) h := by
  rw [mem_stage, rank_evalOO, ← Nat.lt_succ_iff]
  exact rank_lt_iff_criticalOO C B x b q a d (n + 1) h

def boundaryLiftOO (q : SimplexCategoryᵒᵖ) (a d : C.Obj) (n : ℕ)
    (h : RawOO C B x b q a d (n + 1))
    (hc : criticalOO C B x b q a d (n + 1) h) :
    ((stage C B x b false n (leftObj C B x b a) (leftObj C B x b d)).toSSet.obj q) :=
  ⟨evalOO C B x b q a d (n + 1) h,
    (evalOO_mem_previous_iff C B x b q a d n h).2 hc⟩

theorem evalOO_interior_injective (q : SimplexCategoryᵒᵖ) (a d : C.Obj) (r : ℕ)
    (h k : InteriorOO C B x b q a d r)
    (he : evalOO C B x b q a d r h.val = evalOO C B x b q a d r k.val) :
    h.val = k.val := by
  have hn := congrArg (homEquiv C B x b q (leftObj C B x b a) (leftObj C B x b d)) he
  simp only [evalOO, homEquiv_mk] at hn
  exact congrArg Subtype.val (unpadOO_injective C B x b q a d r hn)

theorem evalOO_covers_rank (q : SimplexCategoryᵒᵖ) (a d : C.Obj) (r : ℕ)
    (h : SimplicialCat.HomQuotient.HomObj (relations C B x b) q (leftObj C B x b a) (leftObj C
        B x b d))
    (hr : rankOf C B x b false q h = r) :
    ∃ k : InteriorOO C B x b q a d r, evalOO C B x b q a d r k.val = h := by
  let p : NormalOOAtRank C B x b q a d r := ⟨homEquiv C B x b q _ _ h, hr⟩
  refine ⟨padOO C B x b q a d r p, ?_⟩
  apply (homEquiv C B x b q _ _).injective
  simp only [evalOO, homEquiv_mk]
  exact (padOO_spec C B x b q a d r p).2

def evalON (q : SimplexCategoryᵒᵖ) (a : C.Obj) (w : B.Obj) (r : ℕ)
    (h : RawON C B x b q a w r) :
    SimplicialCat.HomQuotient.HomObj (relations C B x b) q (leftObj C B x b a) (rightObj C B x
        b w) :=
  SimplicialCat.HomQuotient.mk _ q (decodeON C B x b q a w r h)

theorem rank_evalON (q : SimplexCategoryᵒᵖ) (a : C.Obj) (w : B.Obj) (r : ℕ)
    (h : RawON C B x b q a w r) :
    rankOf C B x b true q (evalON C B x b q a w r h) =
      (rightCount C B x b q (normalize C B x b (decodeON C B x b q a w r h)).val).pred := by
  simp [evalON, rankOf, predRank, rank, homEquiv_mk]

theorem evalON_mem_stage (q : SimplexCategoryᵒᵖ) (a : C.Obj) (w : B.Obj) (r : ℕ)
    (h : RawON C B x b q a w r) :
    evalON C B x b q a w r h ∈ (stage C B x b true r (leftObj C B x b a) (rightObj C B x b
        w)).obj q := by
  rw [mem_stage, rank_evalON]
  exact rank_decodeON_le C B x b q a w r h

theorem evalON_mem_previous_iff (q : SimplexCategoryᵒᵖ) (a : C.Obj) (w : B.Obj) (hw : w ≠ b) (n : ℕ)
    (h : RawON C B x b q a w (n + 1)) :
    evalON C B x b q a w (n + 1) h ∈
        (stage C B x b true n (leftObj C B x b a) (rightObj C B x b w)).obj q ↔
      criticalON C B x b q a w (n + 1) h := by
  rw [mem_stage, rank_evalON, ← Nat.lt_succ_iff]
  exact rank_lt_iff_criticalON C B x b q a w hw (n + 1) h

def boundaryLiftON (q : SimplexCategoryᵒᵖ) (a : C.Obj) (w : B.Obj) (hw : w ≠ b) (n : ℕ)
    (h : RawON C B x b q a w (n + 1))
    (hc : criticalON C B x b q a w (n + 1) h) :
    ((stage C B x b true n (leftObj C B x b a) (rightObj C B x b w)).toSSet.obj q) :=
  ⟨evalON C B x b q a w (n + 1) h,
    (evalON_mem_previous_iff C B x b q a w hw n h).2 hc⟩

theorem evalON_interior_injective (q : SimplexCategoryᵒᵖ) (a : C.Obj) (w : B.Obj) (hw : w ≠ b)
    (r : ℕ)
    (h k : InteriorON C B x b q a w r)
    (he : evalON C B x b q a w r h.val = evalON C B x b q a w r k.val) :
    h.val = k.val := by
  have hn := congrArg (homEquiv C B x b q (leftObj C B x b a) (rightObj C B x b w)) he
  simp only [evalON, homEquiv_mk] at hn
  exact congrArg Subtype.val (unpadON_injective C B x b q a w hw r hn)

theorem evalON_covers_rank (q : SimplexCategoryᵒᵖ) (a : C.Obj) (w : B.Obj) (hw : w ≠ b) (r : ℕ)
    (h : SimplicialCat.HomQuotient.HomObj (relations C B x b) q (leftObj C B x b a) (rightObj C
        B x b w))
    (hr : rankOf C B x b true q h = r) :
    ∃ k : InteriorON C B x b q a w r, evalON C B x b q a w r k.val = h := by
  let p : NormalONAtRank C B x b q a w r := ⟨homEquiv C B x b q _ _ h, hr⟩
  refine ⟨padON C B x b q a w hw r p, ?_⟩
  apply (homEquiv C B x b q _ _).injective
  simp only [evalON, homEquiv_mk]
  exact (padON_spec C B x b q a w hw r p).2

def evalNO (q : SimplexCategoryᵒᵖ) (z : B.Obj) (d : C.Obj) (r : ℕ)
    (h : RawNO C B x b q z d r) :
    SimplicialCat.HomQuotient.HomObj (relations C B x b) q (rightObj C B x b z) (leftObj C B x
        b d) :=
  SimplicialCat.HomQuotient.mk _ q (decodeNO C B x b q z d r h)

theorem rank_evalNO (q : SimplexCategoryᵒᵖ) (z : B.Obj) (d : C.Obj) (r : ℕ)
    (h : RawNO C B x b q z d r) :
    rankOf C B x b true q (evalNO C B x b q z d r h) =
      (rightCount C B x b q (normalize C B x b (decodeNO C B x b q z d r h)).val).pred := by
  simp [evalNO, rankOf, predRank, rank, homEquiv_mk]

theorem evalNO_mem_stage (q : SimplexCategoryᵒᵖ) (z : B.Obj) (d : C.Obj) (r : ℕ)
    (h : RawNO C B x b q z d r) :
    evalNO C B x b q z d r h ∈ (stage C B x b true r (rightObj C B x b z) (leftObj C B x b
        d)).obj q := by
  rw [mem_stage, rank_evalNO]
  exact rank_decodeNO_le C B x b q z d r h

theorem evalNO_mem_previous_iff (q : SimplexCategoryᵒᵖ) (z : B.Obj) (d : C.Obj) (hz : z ≠ b) (n : ℕ)
    (h : RawNO C B x b q z d (n + 1)) :
    evalNO C B x b q z d (n + 1) h ∈
        (stage C B x b true n (rightObj C B x b z) (leftObj C B x b d)).obj q ↔
      criticalNO C B x b q z d (n + 1) h := by
  rw [mem_stage, rank_evalNO, ← Nat.lt_succ_iff]
  exact rank_lt_iff_criticalNO C B x b q z hz d (n + 1) h

def boundaryLiftNO (q : SimplexCategoryᵒᵖ) (z : B.Obj) (d : C.Obj) (hz : z ≠ b) (n : ℕ)
    (h : RawNO C B x b q z d (n + 1))
    (hc : criticalNO C B x b q z d (n + 1) h) :
    ((stage C B x b true n (rightObj C B x b z) (leftObj C B x b d)).toSSet.obj q) :=
  ⟨evalNO C B x b q z d (n + 1) h,
    (evalNO_mem_previous_iff C B x b q z d hz n h).2 hc⟩

theorem evalNO_interior_injective (q : SimplexCategoryᵒᵖ) (z : B.Obj) (d : C.Obj) (hz : z ≠ b)
    (r : ℕ)
    (h k : InteriorNO C B x b q z d r)
    (he : evalNO C B x b q z d r h.val = evalNO C B x b q z d r k.val) :
    h.val = k.val := by
  have hn := congrArg (homEquiv C B x b q (rightObj C B x b z) (leftObj C B x b d)) he
  simp only [evalNO, homEquiv_mk] at hn
  exact congrArg Subtype.val (unpadNO_injective C B x b q z hz d r hn)

theorem evalNO_covers_rank (q : SimplexCategoryᵒᵖ) (z : B.Obj) (d : C.Obj) (hz : z ≠ b) (r : ℕ)
    (h : SimplicialCat.HomQuotient.HomObj (relations C B x b) q (rightObj C B x b z) (leftObj C
        B x b d))
    (hr : rankOf C B x b true q h = r) :
    ∃ k : InteriorNO C B x b q z d r, evalNO C B x b q z d r k.val = h := by
  let p : NormalNOAtRank C B x b q z d r := ⟨homEquiv C B x b q _ _ h, hr⟩
  refine ⟨padNO C B x b q z hz d r p, ?_⟩
  apply (homEquiv C B x b q _ _).injective
  simp only [evalNO, homEquiv_mk]
  exact (padNO_spec C B x b q z hz d r p).2

def evalNN (q : SimplexCategoryᵒᵖ) (z w : B.Obj) (r : ℕ)
    (h : RawNN C B x b q z w r) :
    SimplicialCat.HomQuotient.HomObj (relations C B x b) q (rightObj C B x b z) (rightObj C B x
        b w) :=
  SimplicialCat.HomQuotient.mk _ q (decodeNN C B x b q z w r h)

theorem rank_evalNN (q : SimplexCategoryᵒᵖ) (z w : B.Obj) (r : ℕ)
    (h : RawNN C B x b q z w r) :
    rankOf C B x b true q (evalNN C B x b q z w r h) =
      (rightCount C B x b q (normalize C B x b (decodeNN C B x b q z w r h)).val).pred := by
  simp [evalNN, rankOf, predRank, rank, homEquiv_mk]

theorem evalNN_mem_stage (q : SimplexCategoryᵒᵖ) (z w : B.Obj) (r : ℕ)
    (h : RawNN C B x b q z w r) :
    evalNN C B x b q z w r h ∈ (stage C B x b true r (rightObj C B x b z) (rightObj C B x b
        w)).obj q := by
  rw [mem_stage, rank_evalNN]
  exact rank_decodeNN_le C B x b q z w r h

theorem evalNN_mem_previous_iff (q : SimplexCategoryᵒᵖ) (z w : B.Obj) (hz : z ≠ b) (hw : w ≠ b)
    (n : ℕ)
    (h : RawNN C B x b q z w (n + 1)) :
    evalNN C B x b q z w (n + 1) h ∈
        (stage C B x b true n (rightObj C B x b z) (rightObj C B x b w)).obj q ↔
      criticalNN C B x b q z w (n + 1) h := by
  rw [mem_stage, rank_evalNN, ← Nat.lt_succ_iff]
  exact rank_lt_iff_criticalNN C B x b q z w hz hw (n + 1) h

def boundaryLiftNN (q : SimplexCategoryᵒᵖ) (z w : B.Obj) (hz : z ≠ b) (hw : w ≠ b) (n : ℕ)
    (h : RawNN C B x b q z w (n + 1))
    (hc : criticalNN C B x b q z w (n + 1) h) :
    ((stage C B x b true n (rightObj C B x b z) (rightObj C B x b w)).toSSet.obj q) :=
  ⟨evalNN C B x b q z w (n + 1) h,
    (evalNN_mem_previous_iff C B x b q z w hz hw n h).2 hc⟩

theorem evalNN_interior_injective (q : SimplexCategoryᵒᵖ) (z w : B.Obj) (hz : z ≠ b) (hw : w ≠
    b) (r : ℕ)
    (h k : InteriorNN C B x b q z w r)
    (he : evalNN C B x b q z w r h.val = evalNN C B x b q z w r k.val) :
    h.val = k.val := by
  have hn := congrArg (homEquiv C B x b q (rightObj C B x b z) (rightObj C B x b w)) he
  simp only [evalNN, homEquiv_mk] at hn
  exact congrArg Subtype.val (unpadNN_injective C B x b q z w hz hw r hn)

theorem evalNN_covers_rank (q : SimplexCategoryᵒᵖ) (z w : B.Obj) (hz : z ≠ b) (hw : w ≠ b) (r : ℕ)
    (h : SimplicialCat.HomQuotient.HomObj (relations C B x b) q (rightObj C B x b z) (rightObj
        C B x b w))
    (hr : rankOf C B x b true q h = r) :
    ∃ k : InteriorNN C B x b q z w r, evalNN C B x b q z w r k.val = h := by
  let p : NormalNNAtRank C B x b q z w r := ⟨homEquiv C B x b q _ _ h, hr⟩
  refine ⟨padNN C B x b q z w hz hw r p, ?_⟩
  apply (homEquiv C B x b q _ _).injective
  simp only [evalNN, homEquiv_mk]
  exact (padNN_spec C B x b q z w hz hw r p).2

/-- Every primitive face lives in the ACTUAL previous subtype, with the same quotient element. -/
def UnitFaceData.stageFace {q : SimplexCategoryᵒᵖ} {s t : Objects C B x b}
    {p : Path C B x b q s t} {unit : DaggerAmalgamPresentation.Edge C B q}
    (d : UnitFaceData C B x b p unit) (shift : Bool) (n : ℕ)
    (hh : SimplicialCat.HomQuotient.mk (relations C B x b) q p ∈
      (stage C B x b shift n s t).obj q) :
    (stage C B x b shift n s t).toSSet.obj q :=
  ⟨SimplicialCat.HomQuotient.mk (relations C B x b) q d.face,
    d.same_quotient C B x b ▸ hh⟩

/-- Multiple unit faces agree in the SAME previous stage, including all cascades. -/
theorem UnitFaceData.stageFace_overlap {q : SimplexCategoryᵒᵖ} {s t : Objects C B x b}
    {p : Path C B x b q s t} {unit unit' : DaggerAmalgamPresentation.Edge C B q}
    (d : UnitFaceData C B x b p unit) (d' : UnitFaceData C B x b p unit')
    (shift : Bool) (n : ℕ)
    (hh : SimplicialCat.HomQuotient.mk (relations C B x b) q p ∈
      (stage C B x b shift n s t).obj q) :
    d.stageFace C B x b shift n hh = d'.stageFace C B x b shift n hh := by
  apply Subtype.ext
  exact (d.same_quotient C B x b).symm.trans (d'.same_quotient C B x b)

end
end DaggerAmalgamPaddedClassifier
