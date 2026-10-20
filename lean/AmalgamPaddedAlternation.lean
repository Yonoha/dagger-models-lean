import AmalgamPaddedPad

/-! All four raw decoders are literally alternating, including their original endpoint padding. -/

open CategoryTheory DaggerModels DaggerAmalgamPresentation DaggerAmalgamReduction
open DaggerAmalgamPaddedClassification

universe u
namespace DaggerAmalgamPaddedClassifier
noncomputable section
set_option autoImplicit false
variable (C B : SimplicialCat.{u, u}) (x : C.Obj) (b : B.Obj)

theorem headColor_zig_C {q : SimplexCategoryᵒᵖ} {a : C.Obj} (n : ℕ)
    (us : Fin n → (b ⟶[SSet] b).obj q) (vs : Fin n → (x ⟶[SSet] x).obj q)
    (h : (a ⟶[SSet] x).obj q) :
    (encode C B x b (zig C B x b q n us vs) ++ [tag C B q false h]).head?.map
      (fun e ↦ e.1) = some false := by
  cases n <;> simp [zig, encode_comp]
  all_goals rfl

theorem headColor_zag_B {q : SimplexCategoryᵒᵖ} {z : B.Obj} (n : ℕ)
    (vs : Fin n → (x ⟶[SSet] x).obj q) (us : Fin n → (b ⟶[SSet] b).obj q)
    (h : (z ⟶[SSet] b).obj q) :
    (encode C B x b (zag C B x b q n vs us) ++ [tag C B q true h]).head?.map
      (fun e ↦ e.1) = some true := by
  cases n <;> simp [zag, encode_comp, encode_bLoop]
  all_goals rfl

theorem alternating_zig_C {q : SimplexCategoryᵒᵖ} {a : C.Obj}
    (h : (a ⟶[SSet] x).obj q) : ∀ (n : ℕ)
      (us : Fin n → (b ⟶[SSet] b).obj q) (vs : Fin n → (x ⟶[SSet] x).obj q),
    Alternating C B (encode C B x b (zig C B x b q n us vs) ++ [tag C B q false h]) := by
  intro n
  induction n with
  | zero => intro us vs; trivial
  | succ n ih =>
    intro us vs
    let l := encode C B x b (zig C B x b q n
      (fun i ↦ us i.castSucc) (fun i ↦ vs i.castSucc)) ++ [tag C B q false h]
    have hb := alternating_cons C B l (tag C B q true (us (Fin.last n)))
      (ih _ _) (by rw [headColor_zig_C]; simp [tag])
    have hc := alternating_cons C B (tag C B q true (us (Fin.last n)) :: l)
      (tag C B q false (vs (Fin.last n))) hb (by simp [tag])
    simpa only [zig, encode_comp, encode_factorPath, encode_bLoop,
      List.singleton_append, List.cons_append] using hc

theorem alternating_zag_B {q : SimplexCategoryᵒᵖ} {z : B.Obj}
    (h : (z ⟶[SSet] b).obj q) : ∀ (n : ℕ)
      (vs : Fin n → (x ⟶[SSet] x).obj q) (us : Fin n → (b ⟶[SSet] b).obj q),
    Alternating C B (encode C B x b (zag C B x b q n vs us) ++ [tag C B q true h]) := by
  intro n
  induction n with
  | zero => intro vs us; trivial
  | succ n ih =>
    intro vs us
    let l := encode C B x b (zag C B x b q n
      (fun i ↦ vs i.castSucc) (fun i ↦ us i.castSucc)) ++ [tag C B q true h]
    have hc := alternating_cons C B l (tag C B q false (vs (Fin.last n)))
      (ih _ _) (by rw [headColor_zag_B]; simp [tag])
    have hb := alternating_cons C B (tag C B q false (vs (Fin.last n)) :: l)
      (tag C B q true (us (Fin.last n))) hc (by simp [tag])
    simpa only [zag, encode_comp, encode_factorPath, encode_bLoop,
      List.singleton_append, List.cons_append] using hb

theorem alternating_decodeOO (q : SimplexCategoryᵒᵖ) (a d : C.Obj) (r : ℕ)
    (h : RawOO C B x b q a d r) :
    Alternating C B (encode C B x b (decodeOO C B x b q a d r h)) := by
  cases r with
  | zero => trivial
  | succ n =>
    let l := encode C B x b (zig C B x b q n (fun i ↦ h.2.1 i.castSucc) h.2.2.1) ++
      [tag C B q false h.1]
    have hb := alternating_cons C B l (tag C B q true (h.2.1 (Fin.last n)))
      (alternating_zig_C C B x b h.1 n _ _) (by rw [headColor_zig_C]; simp [tag])
    have hc := alternating_cons C B (tag C B q true (h.2.1 (Fin.last n)) :: l)
      (tag C B q false h.2.2.2) hb (by simp [tag])
    simpa only [decodeOO, encode_comp, encode_factorPath, encode_bLoop,
      List.singleton_append, List.cons_append] using hc

theorem alternating_decodeON (q : SimplexCategoryᵒᵖ) (a : C.Obj) (w : B.Obj) (r : ℕ)
    (h : RawON C B x b q a w r) :
    Alternating C B (encode C B x b (decodeON C B x b q a w r h)) := by
  have hb := alternating_cons C B
    (encode C B x b (zig C B x b q r h.2.1 h.2.2.1) ++ [tag C B q false h.1])
    (tag C B q true h.2.2.2) (alternating_zig_C C B x b h.1 r _ _)
    (by rw [headColor_zig_C]; simp [tag])
  simpa only [decodeON, encode_comp, encode_factorPath, encode_bEnd,
    List.singleton_append] using hb

theorem alternating_decodeNO (q : SimplexCategoryᵒᵖ) (z : B.Obj) (d : C.Obj) (r : ℕ)
    (h : RawNO C B x b q z d r) :
    Alternating C B (encode C B x b (decodeNO C B x b q z d r h)) := by
  have hc := alternating_cons C B
    (encode C B x b (zag C B x b q r h.2.1 h.2.2.1) ++ [tag C B q true h.1])
    (tag C B q false h.2.2.2) (alternating_zag_B C B x b h.1 r _ _)
    (by rw [headColor_zag_B]; simp [tag])
  simpa only [decodeNO, encode_comp, encode_factorPath, encode_bStart,
    List.singleton_append] using hc

theorem alternating_decodeNN (q : SimplexCategoryᵒᵖ) (z w : B.Obj) (r : ℕ)
    (h : RawNN C B x b q z w r) :
    Alternating C B (encode C B x b (decodeNN C B x b q z w r h)) := by
  cases r with
  | zero => trivial
  | succ n =>
    let l := encode C B x b (zag C B x b q n (fun i ↦ h.2.1 i.castSucc) h.2.2.1) ++
      [tag C B q true h.1]
    have hc := alternating_cons C B l (tag C B q false (h.2.1 (Fin.last n)))
      (alternating_zag_B C B x b h.1 n _ _) (by rw [headColor_zag_B]; simp [tag])
    have hb := alternating_cons C B (tag C B q false (h.2.1 (Fin.last n)) :: l)
      (tag C B q true h.2.2.2) hc (by simp [tag])
    simpa only [decodeNN, encode_comp, encode_factorPath, encode_bLoop, encode_bStart,
      encode_bEnd, List.singleton_append, List.cons_append] using hb

end
end DaggerAmalgamPaddedClassifier
