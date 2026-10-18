import AmalgamPaddedSurjection
import AmalgamPaddedInteriorCount

/-! Full four-family equivalences, with literal whole tuple and dependent-path inverse laws. -/

open CategoryTheory DaggerModels DaggerAmalgamPresentation
open DaggerAmalgamPaddedClassification DaggerAmalgamNormalForms DaggerAmalgamPathMeasure

universe u
namespace DaggerAmalgamPaddedClassifier
noncomputable section
set_option autoImplicit false
variable (C B : SimplicialCat.{u, u}) (x : C.Obj) (b : B.Obj)

abbrev NormalOOAtRank (q : SimplexCategoryᵒᵖ) (a d : C.Obj) (r : ℕ) :=
  {p : NormalPath C B x b q (leftObj C B x b a) (leftObj C B x b d) //
    rightCount C B x b q p.val = r}
abbrev NormalONAtRank (q : SimplexCategoryᵒᵖ) (a : C.Obj) (w : B.Obj) (r : ℕ) :=
  {p : NormalPath C B x b q (leftObj C B x b a) (rightObj C B x b w) //
    (rightCount C B x b q p.val).pred = r}
abbrev NormalNOAtRank (q : SimplexCategoryᵒᵖ) (z : B.Obj) (d : C.Obj) (r : ℕ) :=
  {p : NormalPath C B x b q (rightObj C B x b z) (leftObj C B x b d) //
    (rightCount C B x b q p.val).pred = r}
abbrev NormalNNAtRank (q : SimplexCategoryᵒᵖ) (z w : B.Obj) (r : ℕ) :=
  {p : NormalPath C B x b q (rightObj C B x b z) (rightObj C B x b w) //
    (rightCount C B x b q p.val).pred = r}

def padOO (q : SimplexCategoryᵒᵖ) (a d : C.Obj) (r : ℕ)
    (p : NormalOOAtRank C B x b q a d r) : InteriorOO C B x b q a d r :=
  Classical.choose (exists_interior_OO C B x b q a d r p.val p.property)

theorem padOO_spec (q : SimplexCategoryᵒᵖ) (a d : C.Obj) (r : ℕ)
    (p : NormalOOAtRank C B x b q a d r) :
    decodeOO C B x b q a d r (padOO C B x b q a d r p).val =
      padPath C B x b false false a d p.val.val ∧
        unpadOO C B x b q a d r (padOO C B x b q a d r p) = p.val :=
  Classical.choose_spec (exists_interior_OO C B x b q a d r p.val p.property)

def equivOO (q : SimplexCategoryᵒᵖ) (a d : C.Obj) (r : ℕ) :
    InteriorOO C B x b q a d r ≃ NormalOOAtRank C B x b q a d r where
  toFun h := ⟨unpadOO C B x b q a d r h, count_normalize_OO C B x b q a d r h.val h.property⟩
  invFun := padOO C B x b q a d r
  left_inv _h := unpadOO_injective C B x b q a d r (padOO_spec C B x b q a d r _).2
  right_inv p := Subtype.ext (padOO_spec C B x b q a d r p).2

theorem pad_unpadOO_tuple (q : SimplexCategoryᵒᵖ) (a d : C.Obj) (r : ℕ)
    (h : InteriorOO C B x b q a d r) :
    (padOO C B x b q a d r (equivOO C B x b q a d r h)).val = h.val :=
  congrArg Subtype.val ((equivOO C B x b q a d r).left_inv h)

theorem unpad_padOO_path (q : SimplexCategoryᵒᵖ) (a d : C.Obj) (r : ℕ)
    (p : NormalOOAtRank C B x b q a d r) :
    (unpadOO C B x b q a d r (padOO C B x b q a d r p)).val = p.val.val :=
  congrArg Subtype.val (padOO_spec C B x b q a d r p).2

def padON (q : SimplexCategoryᵒᵖ) (a : C.Obj) (w : B.Obj) (hw : w ≠ b) (r : ℕ)
    (p : NormalONAtRank C B x b q a w r) : InteriorON C B x b q a w r :=
  Classical.choose (exists_interior_ON C B x b q a w hw r p.val p.property)

theorem padON_spec (q : SimplexCategoryᵒᵖ) (a : C.Obj) (w : B.Obj) (hw : w ≠ b) (r : ℕ)
    (p : NormalONAtRank C B x b q a w r) :
    decodeON C B x b q a w r (padON C B x b q a w hw r p).val =
      padPath C B x b false true a w p.val.val ∧
        unpadON C B x b q a w r (padON C B x b q a w hw r p) = p.val :=
  Classical.choose_spec (exists_interior_ON C B x b q a w hw r p.val p.property)

def equivON (q : SimplexCategoryᵒᵖ) (a : C.Obj) (w : B.Obj) (hw : w ≠ b) (r : ℕ) :
    InteriorON C B x b q a w r ≃ NormalONAtRank C B x b q a w r where
  toFun h := ⟨unpadON C B x b q a w r h,
    by
      simpa only [Nat.pred_succ] using congrArg Nat.pred
        (count_normalize_ON C B x b q a w hw r h.val h.property)⟩
  invFun := padON C B x b q a w hw r
  left_inv _h := unpadON_injective C B x b q a w hw r (padON_spec C B x b q a w hw r _).2
  right_inv p := Subtype.ext (padON_spec C B x b q a w hw r p).2

theorem pad_unpadON_tuple (q : SimplexCategoryᵒᵖ) (a : C.Obj) (w : B.Obj) (hw : w ≠ b)
    (r : ℕ) (h : InteriorON C B x b q a w r) :
    (padON C B x b q a w hw r (equivON C B x b q a w hw r h)).val = h.val :=
  congrArg Subtype.val ((equivON C B x b q a w hw r).left_inv h)

theorem unpad_padON_path (q : SimplexCategoryᵒᵖ) (a : C.Obj) (w : B.Obj) (hw : w ≠ b)
    (r : ℕ) (p : NormalONAtRank C B x b q a w r) :
    (unpadON C B x b q a w r (padON C B x b q a w hw r p)).val = p.val.val :=
  congrArg Subtype.val (padON_spec C B x b q a w hw r p).2

def padNO (q : SimplexCategoryᵒᵖ) (z : B.Obj) (hz : z ≠ b) (d : C.Obj) (r : ℕ)
    (p : NormalNOAtRank C B x b q z d r) : InteriorNO C B x b q z d r :=
  Classical.choose (exists_interior_NO C B x b q z hz d r p.val p.property)

theorem padNO_spec (q : SimplexCategoryᵒᵖ) (z : B.Obj) (hz : z ≠ b) (d : C.Obj) (r : ℕ)
    (p : NormalNOAtRank C B x b q z d r) :
    decodeNO C B x b q z d r (padNO C B x b q z hz d r p).val =
      padPath C B x b true false z d p.val.val ∧
        unpadNO C B x b q z d r (padNO C B x b q z hz d r p) = p.val :=
  Classical.choose_spec (exists_interior_NO C B x b q z hz d r p.val p.property)

def equivNO (q : SimplexCategoryᵒᵖ) (z : B.Obj) (hz : z ≠ b) (d : C.Obj) (r : ℕ) :
    InteriorNO C B x b q z d r ≃ NormalNOAtRank C B x b q z d r where
  toFun h := ⟨unpadNO C B x b q z d r h,
    by
      simpa only [Nat.pred_succ] using congrArg Nat.pred
        (count_normalize_NO C B x b q z hz d r h.val h.property)⟩
  invFun := padNO C B x b q z hz d r
  left_inv _h := unpadNO_injective C B x b q z hz d r (padNO_spec C B x b q z hz d r _).2
  right_inv p := Subtype.ext (padNO_spec C B x b q z hz d r p).2

theorem pad_unpadNO_tuple (q : SimplexCategoryᵒᵖ) (z : B.Obj) (hz : z ≠ b) (d : C.Obj)
    (r : ℕ) (h : InteriorNO C B x b q z d r) :
    (padNO C B x b q z hz d r (equivNO C B x b q z hz d r h)).val = h.val :=
  congrArg Subtype.val ((equivNO C B x b q z hz d r).left_inv h)

theorem unpad_padNO_path (q : SimplexCategoryᵒᵖ) (z : B.Obj) (hz : z ≠ b) (d : C.Obj)
    (r : ℕ) (p : NormalNOAtRank C B x b q z d r) :
    (unpadNO C B x b q z d r (padNO C B x b q z hz d r p)).val = p.val.val :=
  congrArg Subtype.val (padNO_spec C B x b q z hz d r p).2

def padNN (q : SimplexCategoryᵒᵖ) (z w : B.Obj) (hz : z ≠ b) (hw : w ≠ b) (r : ℕ)
    (p : NormalNNAtRank C B x b q z w r) : InteriorNN C B x b q z w r :=
  Classical.choose (exists_interior_NN C B x b q z w hz hw r p.val p.property)

theorem padNN_spec (q : SimplexCategoryᵒᵖ) (z w : B.Obj) (hz : z ≠ b) (hw : w ≠ b) (r : ℕ)
    (p : NormalNNAtRank C B x b q z w r) :
    decodeNN C B x b q z w r (padNN C B x b q z w hz hw r p).val =
      padPath C B x b true true z w p.val.val ∧
        unpadNN C B x b q z w r (padNN C B x b q z w hz hw r p) = p.val :=
  Classical.choose_spec (exists_interior_NN C B x b q z w hz hw r p.val p.property)

def equivNN (q : SimplexCategoryᵒᵖ) (z w : B.Obj) (hz : z ≠ b) (hw : w ≠ b) (r : ℕ) :
    InteriorNN C B x b q z w r ≃ NormalNNAtRank C B x b q z w r where
  toFun h := ⟨unpadNN C B x b q z w r h,
    predCount_normalize_NN C B x b q z w hz hw r h.val h.property⟩
  invFun := padNN C B x b q z w hz hw r
  left_inv _h := unpadNN_injective C B x b q z w hz hw r (padNN_spec C B x b q z w hz hw r _).2
  right_inv p := Subtype.ext (padNN_spec C B x b q z w hz hw r p).2

theorem pad_unpadNN_tuple (q : SimplexCategoryᵒᵖ) (z w : B.Obj) (hz : z ≠ b) (hw : w ≠ b)
    (r : ℕ) (h : InteriorNN C B x b q z w r) :
    (padNN C B x b q z w hz hw r (equivNN C B x b q z w hz hw r h)).val = h.val :=
  congrArg Subtype.val ((equivNN C B x b q z w hz hw r).left_inv h)

theorem unpad_padNN_path (q : SimplexCategoryᵒᵖ) (z w : B.Obj) (hz : z ≠ b) (hw : w ≠ b)
    (r : ℕ) (p : NormalNNAtRank C B x b q z w r) :
    (unpadNN C B x b q z w r (padNN C B x b q z w hz hw r p)).val = p.val.val :=
  congrArg Subtype.val (padNN_spec C B x b q z w hz hw r p).2

end
end DaggerAmalgamPaddedClassifier
