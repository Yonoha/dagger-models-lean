import AmalgamPaddedFaces
import AmalgamPaddedCoordinateSlots

/-! Each supplied Fin index is retained in the primitive delete/compose face. -/

open CategoryTheory DaggerModels DaggerAmalgamPresentation DaggerAmalgamReduction
open DaggerAmalgamPaddedClassification DaggerAmalgamNormalForms DaggerAmalgamPathMeasure

universe u
namespace DaggerAmalgamPaddedClassifier
noncomputable section
set_option autoImplicit false
variable (C B : SimplicialCat.{u, u}) (x : C.Obj) (b : B.Obj)

structure IndexedUnitFaceData {q : SimplexCategoryᵒᵖ} {s t : Objects C B x b}
    (k : ℕ) (p : Path C B x b q s t) (unit : Edge C B q)
    extends UnitFaceData C B x b p unit where
  position : pre.length + 1 = k

theorem exists_indexedUnitFace {q : SimplexCategoryᵒᵖ} {s t : Objects C B x b}
    (k : ℕ) (p : Path C B x b q s t) (unit : Edge C B q)
    (ha : Alternating C B (encode C B x b p)) (hi : IsIdentity C B q unit)
    (ho : SlotOccurrence C B k unit (encode C B x b p)) :
    Nonempty (IndexedUnitFaceData C B x b k p unit) := by
  rcases ho with ⟨pre, left, right, post, he, hpos⟩
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
  exact ⟨⟨⟨pre, left, right, post, composed, pd, pf, he, hi, hm, hpd, hed, hpf, hef,
    hcount, (normalize_finite C B x b (.single hpd)).trans
      (normalize_finite C B x b (.single hpf))⟩, hpos⟩⟩

def indexedUnitFace {q : SimplexCategoryᵒᵖ} {s t : Objects C B x b}
    (k : ℕ) (p : Path C B x b q s t) (unit : Edge C B q)
    (ha : Alternating C B (encode C B x b p)) (hi : IsIdentity C B q unit)
    (ho : SlotOccurrence C B k unit (encode C B x b p)) :
    IndexedUnitFaceData C B x b k p unit :=
  Classical.choice (exists_indexedUnitFace C B x b k p unit ha hi ho)

/-- Exact predecessor, selected unit, successor, and remaining word order all come from p. -/
def IndexedUnitFaceData.slot {q : SimplexCategoryᵒᵖ} {s t : Objects C B x b} {k : ℕ}
    {p : Path C B x b q s t} {unit : Edge C B q}
    (d : IndexedUnitFaceData C B x b k p unit) :
    SlotOccurrence C B k unit (encode C B x b p) :=
  ⟨d.pre, d.left, d.right, d.post, d.original_encode, d.position⟩

theorem IndexedUnitFaceData.normal_count_lt {q : SimplexCategoryᵒᵖ}
    {s t : Objects C B x b} {k : ℕ} {p : Path C B x b q s t} {unit : Edge C B q}
    (d : IndexedUnitFaceData C B x b k p unit) :
    rightCount C B x b q (normalize C B x b p).val < rightCount C B x b q p :=
  d.toUnitFaceData.normal_count_lt C B x b

end
end DaggerAmalgamPaddedClassifier
