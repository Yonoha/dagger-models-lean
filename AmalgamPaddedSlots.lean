import AmalgamPaddedOccurrences

/-! Position-bound critical coordinate contexts; repeated identical unit VALUES stay distinct. -/

open CategoryTheory DaggerModels DaggerAmalgamPresentation DaggerAmalgamReduction
open DaggerAmalgamPaddedClassification

universe u
namespace DaggerAmalgamPaddedClassifier
noncomputable section
set_option autoImplicit false
variable (C B : SimplicialCat.{u, u}) (x : C.Obj) (b : B.Obj)

structure SlotOccurrence {q : SimplexCategoryᵒᵖ} (k : ℕ) (e : Edge C B q)
    (l : List (Edge C B q)) where
  pre : List (Edge C B q)
  left : Edge C B q
  right : Edge C B q
  post : List (Edge C B q)
  whole : l = pre ++ left :: e :: right :: post
  position : pre.length + 1 = k

/-- The frame fixes the literal right neighbor and all remaining letters. -/
def slotAfterHead {q : SimplexCategoryᵒᵖ} (left e d : Edge C B q)
    (post : List (Edge C B q)) :
    SlotOccurrence C B 1 e (left :: e :: d :: post) :=
  ⟨[], left, d, post, rfl, rfl⟩

def slotAfterTwo {q : SimplexCategoryᵒᵖ} (before left e d : Edge C B q)
    (post : List (Edge C B q)) :
    SlotOccurrence C B 2 e (before :: left :: e :: d :: post) :=
  ⟨[before], left, d, post, rfl, rfl⟩

def prependSlot {q : SimplexCategoryᵒᵖ} {k : ℕ} {e : Edge C B q}
    {l : List (Edge C B q)} (a : Edge C B q) (s : SlotOccurrence C B k e l) :
    SlotOccurrence C B (k + 1) e (a :: l) :=
  ⟨a :: s.pre, s.left, s.right, s.post, congrArg (a :: ·) s.whole, by
    simp only [List.length_cons]; have := s.position; omega⟩

def prependTwoSlot {q : SimplexCategoryᵒᵖ} {k : ℕ} {e : Edge C B q}
    {l : List (Edge C B q)} (a d : Edge C B q) (s : SlotOccurrence C B k e l) :
    SlotOccurrence C B (k + 2) e (a :: d :: l) := prependSlot C B a (prependSlot C B d s)

def slotBeforeTail {q : SimplexCategoryᵒᵖ} (left e : Edge C B q)
    (rest : List (Edge C B q)) (hne : rest ≠ []) :
    SlotOccurrence C B 1 e (left :: e :: rest) :=
  ⟨[], left, rest.head hne, rest.tail, by simp only [List.nil_append, List.cons_head_tail], rfl⟩

/-- Both loop slots in each original zig pair, selected by the GIVEN Fin index. -/
def zigSlots (q : SimplexCategoryᵒᵖ) : ∀ (n : ℕ)
    (us : Fin n → (b ⟶[SSet] b).obj q) (vs : Fin n → (x ⟶[SSet] x).obj q)
    (left right : Edge C B q),
    (∀ i, SlotOccurrence C B (2 * (n - 1 - i.val) + 2) (tag C B q true (us i))
      (left :: encode C B x b (zig C B x b q n us vs) ++ [right])) ×
    ∀ i, SlotOccurrence C B (2 * (n - 1 - i.val) + 1) (tag C B q false (vs i))
      (left :: encode C B x b (zig C B x b q n us vs) ++ [right]) := by
  intro n
  induction n with
  | zero => intro us vs left right; exact ⟨fun i ↦ Fin.elim0 i, fun i ↦ Fin.elim0 i⟩
  | succ n ih =>
    intro us vs left right
    let rest := encode C B x b (zig C B x b q n
      (fun i ↦ us i.castSucc) (fun i ↦ vs i.castSucc)) ++ [right]
    obtain ⟨hu, hv⟩ := ih (fun i ↦ us i.castSucc) (fun i ↦ vs i.castSucc)
      (tag C B q true (us (Fin.last n))) right
    have he : left :: encode C B x b (zig C B x b q (n + 1) us vs) ++ [right] =
        left :: tag C B q false (vs (Fin.last n)) :: tag C B q true (us (Fin.last n)) ::
          rest := by simp only [rest, zig, encode_comp, encode_factorPath, encode_bLoop,
            List.cons_append, List.nil_append]
    refine ⟨?_, ?_⟩
    · intro i
      refine Fin.lastCases ?_ (fun j ↦ ?_) i
      · have hp : 2 * (n + 1 - 1 - (Fin.last n).val) + 2 = 2 := by simp
        rw [hp, he]
        exact prependSlot C B left (slotBeforeTail C B _ _ rest (by simp [rest]))
      · have hp : 2 * (n + 1 - 1 - j.castSucc.val) + 2 =
            (2 * (n - 1 - j.val) + 2) + 2 := by have := j.isLt; simp only [Fin.val_castSucc]; omega
        rw [hp, he]
        exact prependTwoSlot C B left (tag C B q false (vs (Fin.last n))) (hu j)
    · intro i
      refine Fin.lastCases ?_ (fun j ↦ ?_) i
      · have hp : 2 * (n + 1 - 1 - (Fin.last n).val) + 1 = 1 := by simp
        rw [hp, he]
        exact slotAfterHead C B left _ _ rest
      · have hp : 2 * (n + 1 - 1 - j.castSucc.val) + 1 =
            (2 * (n - 1 - j.val) + 1) + 2 := by have := j.isLt; simp only [Fin.val_castSucc]; omega
        rw [hp, he]
        exact prependTwoSlot C B left (tag C B q false (vs (Fin.last n))) (hv j)

/-- Both loop slots in each original zag pair, selected by the GIVEN Fin index. -/
def zagSlots (q : SimplexCategoryᵒᵖ) : ∀ (n : ℕ)
    (vs : Fin n → (x ⟶[SSet] x).obj q) (us : Fin n → (b ⟶[SSet] b).obj q)
    (left right : Edge C B q),
    (∀ i, SlotOccurrence C B (2 * (n - 1 - i.val) + 2) (tag C B q false (vs i))
      (left :: encode C B x b (zag C B x b q n vs us) ++ [right])) ×
    ∀ i, SlotOccurrence C B (2 * (n - 1 - i.val) + 1) (tag C B q true (us i))
      (left :: encode C B x b (zag C B x b q n vs us) ++ [right]) := by
  intro n
  induction n with
  | zero => intro vs us left right; exact ⟨fun i ↦ Fin.elim0 i, fun i ↦ Fin.elim0 i⟩
  | succ n ih =>
    intro vs us left right
    let rest := encode C B x b (zag C B x b q n
      (fun i ↦ vs i.castSucc) (fun i ↦ us i.castSucc)) ++ [right]
    obtain ⟨hu, hv⟩ := ih (fun i ↦ vs i.castSucc) (fun i ↦ us i.castSucc)
      (tag C B q false (vs (Fin.last n))) right
    have he : left :: encode C B x b (zag C B x b q (n + 1) vs us) ++ [right] =
        left :: tag C B q true (us (Fin.last n)) :: tag C B q false (vs (Fin.last n)) ::
          rest := by simp only [rest, zag, encode_comp, encode_factorPath, encode_bLoop,
            List.cons_append, List.nil_append]
    refine ⟨?_, ?_⟩
    · intro i
      refine Fin.lastCases ?_ (fun j ↦ ?_) i
      · have hp : 2 * (n + 1 - 1 - (Fin.last n).val) + 2 = 2 := by simp
        rw [hp, he]
        exact prependSlot C B left (slotBeforeTail C B _ _ rest (by simp [rest]))
      · have hp : 2 * (n + 1 - 1 - j.castSucc.val) + 2 =
            (2 * (n - 1 - j.val) + 2) + 2 := by have := j.isLt; simp only [Fin.val_castSucc]; omega
        rw [hp, he]
        exact prependTwoSlot C B left (tag C B q true (us (Fin.last n))) (hu j)
    · intro i
      refine Fin.lastCases ?_ (fun j ↦ ?_) i
      · have hp : 2 * (n + 1 - 1 - (Fin.last n).val) + 1 = 1 := by simp
        rw [hp, he]
        exact slotAfterHead C B left _ _ rest
      · have hp : 2 * (n + 1 - 1 - j.castSucc.val) + 1 =
            (2 * (n - 1 - j.val) + 1) + 2 := by have := j.isLt; simp only [Fin.val_castSucc]; omega
        rw [hp, he]
        exact prependTwoSlot C B left (tag C B q true (us (Fin.last n))) (hv j)

end
end DaggerAmalgamPaddedClassifier
