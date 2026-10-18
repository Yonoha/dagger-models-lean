import AmalgamPaddedEquivalences

/-! Every original critical coordinate occurs strictly between the endpoint padding letters. -/

open CategoryTheory DaggerModels DaggerAmalgamPresentation DaggerAmalgamReduction
open DaggerAmalgamPaddedClassification DaggerAmalgamNormalForms

universe u
namespace DaggerAmalgamPaddedClassifier
noncomputable section
set_option autoImplicit false
variable (C B : SimplicialCat.{u, u}) (x : C.Obj) (b : B.Obj)

def InnerOccurrence {q : SimplexCategoryᵒᵖ} (e : Edge C B q)
    (l : List (Edge C B q)) : Prop :=
  ∃ pre left right post, l = pre ++ left :: e :: right :: post

theorem innerOccurrence_prepend {q : SimplexCategoryᵒᵖ} {e : Edge C B q}
    {l : List (Edge C B q)} (d : Edge C B q) (h : InnerOccurrence C B e l) :
    InnerOccurrence C B e (d :: l) := by
  rcases h with ⟨pre, left, right, post, rfl⟩
  exact ⟨d :: pre, left, right, post, rfl⟩

theorem innerOccurrence_framed {q : SimplexCategoryᵒᵖ} (left right e : Edge C B q)
    (l : List (Edge C B q)) (he : e ∈ l) :
    InnerOccurrence C B e (left :: l ++ [right]) := by
  induction l generalizing left with
  | nil => cases he
  | cons d l ih =>
    rcases List.mem_cons.mp he with rfl | he
    · cases l with
      | nil => exact ⟨[], left, right, [], rfl⟩
      | cons f l => exact ⟨[], left, f, l ++ [right], rfl⟩
    · exact innerOccurrence_prepend C B left (ih d he)

theorem mem_encode_zig (q : SimplexCategoryᵒᵖ) : ∀ (n : ℕ)
    (us : Fin n → (b ⟶[SSet] b).obj q) (vs : Fin n → (x ⟶[SSet] x).obj q),
    (∀ i, tag C B q true (us i) ∈ encode C B x b (zig C B x b q n us vs)) ∧
    ∀ i, tag C B q false (vs i) ∈ encode C B x b (zig C B x b q n us vs) := by
  intro n
  induction n with
  | zero => intro us vs; exact ⟨fun i ↦ Fin.elim0 i, fun i ↦ Fin.elim0 i⟩
  | succ n ih =>
    intro us vs
    simp only [zig, encode_comp, encode_factorPath, encode_bLoop, List.singleton_append]
    obtain ⟨hu, hv⟩ := ih (fun i ↦ us i.castSucc) (fun i ↦ vs i.castSucc)
    refine ⟨?_, ?_⟩
    · intro i
      refine Fin.lastCases ?_ (fun j ↦ ?_) i
      · exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (hu j))
    · intro i
      refine Fin.lastCases ?_ (fun j ↦ ?_) i
      · exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (hv j))

theorem mem_encode_zag (q : SimplexCategoryᵒᵖ) : ∀ (n : ℕ)
    (vs : Fin n → (x ⟶[SSet] x).obj q) (us : Fin n → (b ⟶[SSet] b).obj q),
    (∀ i, tag C B q false (vs i) ∈ encode C B x b (zag C B x b q n vs us)) ∧
    ∀ i, tag C B q true (us i) ∈ encode C B x b (zag C B x b q n vs us) := by
  intro n
  induction n with
  | zero => intro vs us; exact ⟨fun i ↦ Fin.elim0 i, fun i ↦ Fin.elim0 i⟩
  | succ n ih =>
    intro vs us
    simp only [zag, encode_comp, encode_factorPath, encode_bLoop, List.singleton_append]
    obtain ⟨hv, hu⟩ := ih (fun i ↦ vs i.castSucc) (fun i ↦ us i.castSucc)
    refine ⟨?_, ?_⟩
    · intro i
      refine Fin.lastCases ?_ (fun j ↦ ?_) i
      · exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (hv j))
    · intro i
      refine Fin.lastCases ?_ (fun j ↦ ?_) i
      · exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (hu j))

theorem occurrenceOO_B (q : SimplexCategoryᵒᵖ) (a d : C.Obj) (n : ℕ)
    (h : RawOO C B x b q a d (n + 1)) (i : Fin (n + 1)) :
    InnerOccurrence C B (tag C B q true (h.2.1 i))
      (encode C B x b (decodeOO C B x b q a d (n + 1) h)) := by
  simp only [decodeOO, encode_comp, encode_factorPath, encode_bLoop,
    List.cons_append, List.nil_append]
  rw [← List.cons_append]
  apply innerOccurrence_framed
  refine Fin.lastCases (List.mem_cons_self ..) (fun j ↦ ?_) i
  exact List.mem_cons_of_mem _ ((mem_encode_zig C B x b q n _ _).1 j)

theorem occurrenceOO_C (q : SimplexCategoryᵒᵖ) (a d : C.Obj) (n : ℕ)
    (h : RawOO C B x b q a d (n + 1)) (i : Fin n) :
    InnerOccurrence C B (tag C B q false (h.2.2.1 i))
      (encode C B x b (decodeOO C B x b q a d (n + 1) h)) := by
  simp only [decodeOO, encode_comp, encode_factorPath, encode_bLoop,
    List.cons_append, List.nil_append]
  rw [← List.cons_append]
  apply innerOccurrence_framed
  exact List.mem_cons_of_mem _ ((mem_encode_zig C B x b q n _ _).2 i)

theorem occurrenceON_B (q : SimplexCategoryᵒᵖ) (a : C.Obj) (w : B.Obj) (n : ℕ)
    (h : RawON C B x b q a w n) (i : Fin n) :
    InnerOccurrence C B (tag C B q true (h.2.1 i))
      (encode C B x b (decodeON C B x b q a w n h)) := by
  simp only [decodeON, encode_comp, encode_factorPath, encode_bEnd,
    List.singleton_append]
  exact innerOccurrence_framed C B _ _ _ _ ((mem_encode_zig C B x b q n _ _).1 i)

theorem occurrenceON_C (q : SimplexCategoryᵒᵖ) (a : C.Obj) (w : B.Obj) (n : ℕ)
    (h : RawON C B x b q a w n) (i : Fin n) :
    InnerOccurrence C B (tag C B q false (h.2.2.1 i))
      (encode C B x b (decodeON C B x b q a w n h)) := by
  simp only [decodeON, encode_comp, encode_factorPath, encode_bEnd,
    List.singleton_append]
  exact innerOccurrence_framed C B _ _ _ _ ((mem_encode_zig C B x b q n _ _).2 i)

theorem occurrenceNO_C (q : SimplexCategoryᵒᵖ) (z : B.Obj) (d : C.Obj) (n : ℕ)
    (h : RawNO C B x b q z d n) (i : Fin n) :
    InnerOccurrence C B (tag C B q false (h.2.1 i))
      (encode C B x b (decodeNO C B x b q z d n h)) := by
  simp only [decodeNO, encode_comp, encode_factorPath, encode_bStart,
    List.singleton_append]
  exact innerOccurrence_framed C B _ _ _ _ ((mem_encode_zag C B x b q n _ _).1 i)

theorem occurrenceNO_B (q : SimplexCategoryᵒᵖ) (z : B.Obj) (d : C.Obj) (n : ℕ)
    (h : RawNO C B x b q z d n) (i : Fin n) :
    InnerOccurrence C B (tag C B q true (h.2.2.1 i))
      (encode C B x b (decodeNO C B x b q z d n h)) := by
  simp only [decodeNO, encode_comp, encode_factorPath, encode_bStart,
    List.singleton_append]
  exact innerOccurrence_framed C B _ _ _ _ ((mem_encode_zag C B x b q n _ _).2 i)

theorem occurrenceNN_C (q : SimplexCategoryᵒᵖ) (z w : B.Obj) (n : ℕ)
    (h : RawNN C B x b q z w (n + 1)) (i : Fin (n + 1)) :
    InnerOccurrence C B (tag C B q false (h.2.1 i))
      (encode C B x b (decodeNN C B x b q z w (n + 1) h)) := by
  simp only [decodeNN, encode_comp, encode_factorPath, encode_bStart, encode_bEnd,
    List.cons_append, List.nil_append]
  rw [← List.cons_append]
  apply innerOccurrence_framed
  refine Fin.lastCases (List.mem_cons_self ..) (fun j ↦ ?_) i
  exact List.mem_cons_of_mem _ ((mem_encode_zag C B x b q n _ _).1 j)

theorem occurrenceNN_B (q : SimplexCategoryᵒᵖ) (z w : B.Obj) (n : ℕ)
    (h : RawNN C B x b q z w (n + 1)) (i : Fin n) :
    InnerOccurrence C B (tag C B q true (h.2.2.1 i))
      (encode C B x b (decodeNN C B x b q z w (n + 1) h)) := by
  simp only [decodeNN, encode_comp, encode_factorPath, encode_bStart, encode_bEnd,
    List.cons_append, List.nil_append]
  rw [← List.cons_append]
  apply innerOccurrence_framed
  exact List.mem_cons_of_mem _ ((mem_encode_zag C B x b q n _ _).2 i)

end
end DaggerAmalgamPaddedClassifier
