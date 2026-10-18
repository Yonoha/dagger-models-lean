import AmalgamPaddedSlots

/-! All eight exact original coordinate positions, predecessors, successors, and untouched order. -/

open CategoryTheory DaggerModels DaggerAmalgamPresentation DaggerAmalgamReduction
open DaggerAmalgamPaddedClassification

universe u
namespace DaggerAmalgamPaddedClassifier
noncomputable section
set_option autoImplicit false
variable (C B : SimplicialCat.{u, u}) (x : C.Obj) (b : B.Obj)

def slotOO_B (q : SimplexCategoryᵒᵖ) (a d : C.Obj) (n : ℕ)
    (h : RawOO C B x b q a d (n + 1)) (i : Fin (n + 1)) :
    SlotOccurrence C B (2 * (n - i.val) + 1) (tag C B q true (h.2.1 i))
      (encode C B x b (decodeOO C B x b q a d (n + 1) h)) := by
  simp only [decodeOO, encode_comp, encode_factorPath, encode_bLoop,
    List.cons_append, List.nil_append]
  refine Fin.lastCases ?_ (fun j ↦ ?_) i
  · have hp : 2 * (n - (Fin.last n).val) + 1 = 1 := by simp
    rw [hp]
    exact slotBeforeTail C B _ _ _ (by simp)
  · have hp : 2 * (n - j.castSucc.val) + 1 = (2 * (n - 1 - j.val) + 2) + 1 := by
      have := j.isLt; simp only [Fin.val_castSucc]; omega
    rw [hp]
    exact prependSlot C B _ ((zigSlots C B x b q n (fun i ↦ h.2.1 i.castSucc) h.2.2.1
      (tag C B q true (h.2.1 (Fin.last n))) (tag C B q false h.1)).1 j)

def slotOO_C (q : SimplexCategoryᵒᵖ) (a d : C.Obj) (n : ℕ)
    (h : RawOO C B x b q a d (n + 1)) (i : Fin n) :
    SlotOccurrence C B (2 * (n - 1 - i.val) + 2) (tag C B q false (h.2.2.1 i))
      (encode C B x b (decodeOO C B x b q a d (n + 1) h)) := by
  simp only [decodeOO, encode_comp, encode_factorPath, encode_bLoop,
    List.cons_append, List.nil_append]
  exact prependSlot C B _ ((zigSlots C B x b q n _ _ _ _).2 i)

def slotON_B (q : SimplexCategoryᵒᵖ) (a : C.Obj) (w : B.Obj) (n : ℕ)
    (h : RawON C B x b q a w n) (i : Fin n) :
    SlotOccurrence C B (2 * (n - 1 - i.val) + 2) (tag C B q true (h.2.1 i))
      (encode C B x b (decodeON C B x b q a w n h)) := by
  simp only [decodeON, encode_comp, encode_factorPath, encode_bEnd, List.singleton_append]
  exact (zigSlots C B x b q n _ _ _ _).1 i

def slotON_C (q : SimplexCategoryᵒᵖ) (a : C.Obj) (w : B.Obj) (n : ℕ)
    (h : RawON C B x b q a w n) (i : Fin n) :
    SlotOccurrence C B (2 * (n - 1 - i.val) + 1) (tag C B q false (h.2.2.1 i))
      (encode C B x b (decodeON C B x b q a w n h)) := by
  simp only [decodeON, encode_comp, encode_factorPath, encode_bEnd, List.singleton_append]
  exact (zigSlots C B x b q n _ _ _ _).2 i

def slotNO_C (q : SimplexCategoryᵒᵖ) (z : B.Obj) (d : C.Obj) (n : ℕ)
    (h : RawNO C B x b q z d n) (i : Fin n) :
    SlotOccurrence C B (2 * (n - 1 - i.val) + 2) (tag C B q false (h.2.1 i))
      (encode C B x b (decodeNO C B x b q z d n h)) := by
  simp only [decodeNO, encode_comp, encode_factorPath, encode_bStart, List.singleton_append]
  exact (zagSlots C B x b q n _ _ _ _).1 i

def slotNO_B (q : SimplexCategoryᵒᵖ) (z : B.Obj) (d : C.Obj) (n : ℕ)
    (h : RawNO C B x b q z d n) (i : Fin n) :
    SlotOccurrence C B (2 * (n - 1 - i.val) + 1) (tag C B q true (h.2.2.1 i))
      (encode C B x b (decodeNO C B x b q z d n h)) := by
  simp only [decodeNO, encode_comp, encode_factorPath, encode_bStart, List.singleton_append]
  exact (zagSlots C B x b q n _ _ _ _).2 i

def slotNN_C (q : SimplexCategoryᵒᵖ) (z w : B.Obj) (n : ℕ)
    (h : RawNN C B x b q z w (n + 1)) (i : Fin (n + 1)) :
    SlotOccurrence C B (2 * (n - i.val) + 1) (tag C B q false (h.2.1 i))
      (encode C B x b (decodeNN C B x b q z w (n + 1) h)) := by
  simp only [decodeNN, encode_comp, encode_factorPath, encode_bStart, encode_bEnd,
    List.cons_append, List.nil_append]
  refine Fin.lastCases ?_ (fun j ↦ ?_) i
  · have hp : 2 * (n - (Fin.last n).val) + 1 = 1 := by simp
    rw [hp]
    exact slotBeforeTail C B _ _ _ (by simp)
  · have hp : 2 * (n - j.castSucc.val) + 1 = (2 * (n - 1 - j.val) + 2) + 1 := by
      have := j.isLt; simp only [Fin.val_castSucc]; omega
    rw [hp]
    exact prependSlot C B _ ((zagSlots C B x b q n (fun i ↦ h.2.1 i.castSucc) h.2.2.1
      (tag C B q false (h.2.1 (Fin.last n))) (tag C B q true h.1)).1 j)

def slotNN_B (q : SimplexCategoryᵒᵖ) (z w : B.Obj) (n : ℕ)
    (h : RawNN C B x b q z w (n + 1)) (i : Fin n) :
    SlotOccurrence C B (2 * (n - 1 - i.val) + 2) (tag C B q true (h.2.2.1 i))
      (encode C B x b (decodeNN C B x b q z w (n + 1) h)) := by
  simp only [decodeNN, encode_comp, encode_factorPath, encode_bStart, encode_bEnd,
    List.cons_append, List.nil_append]
  exact prependSlot C B _ ((zagSlots C B x b q n _ _ _ _).2 i)

theorem SlotOccurrence.at_index {q : SimplexCategoryᵒᵖ} {k : ℕ} {e : Edge C B q}
    {l : List (Edge C B q)} (s : SlotOccurrence C B k e l) : l[k]? = some e := by
  rcases s with ⟨pre, left, right, post, he, hp⟩
  rw [he, ← hp, List.getElem?_append_right (by omega)]
  simp

theorem SlotOccurrence.predecessor {q : SimplexCategoryᵒᵖ} {k : ℕ} {e : Edge C B q}
    {l : List (Edge C B q)} (s : SlotOccurrence C B k e l) : l[k - 1]? = some s.left := by
  rcases s with ⟨pre, left, right, post, he, hp⟩
  change l[k - 1]? = some left
  rw [he, ← hp, Nat.add_sub_cancel, List.getElem?_append_right (Nat.le_refl _)]
  simp

theorem SlotOccurrence.successor {q : SimplexCategoryᵒᵖ} {k : ℕ} {e : Edge C B q}
    {l : List (Edge C B q)} (s : SlotOccurrence C B k e l) : l[k + 1]? = some s.right := by
  rcases s with ⟨pre, left, right, post, he, hp⟩
  change l[k + 1]? = some right
  rw [he, ← hp, List.getElem?_append_right (by omega)]
  have hk : pre.length + 1 + 1 - pre.length = 2 := by omega
  rw [hk]
  rfl

end
end DaggerAmalgamPaddedClassifier
