import AmalgamPaddedEdges

/-! Appending one full original alternating block to each raw family.
All Fin entries and original endpoint arrows are retained, including rank-zero bases. -/

open CategoryTheory DaggerModels DaggerAmalgamPresentation DaggerAmalgamReduction
open DaggerAmalgamPaddedClassification

universe u

namespace DaggerAmalgamPaddedClassifier

noncomputable section
set_option autoImplicit false

variable (C B : SimplicialCat.{u, u}) (x : C.Obj) (b : B.Obj)

def extendOO (q : SimplexCategoryᵒᵖ) (a d : C.Obj) : (r : ℕ) →
    RawOO C B x b q a x r → (b ⟶[SSet] b).obj q →
      (x ⟶[SSet] d).obj q → RawOO C B x b q a d (r + 1)
  | 0, h, u, k => ⟨h, fun _ ↦ u, Fin.elim0, k⟩
  | _ + 1, h, u, k => ⟨h.1, Fin.snoc h.2.1 u, Fin.snoc h.2.2.1 h.2.2.2, k⟩

def extendON (q : SimplexCategoryᵒᵖ) (a : C.Obj) (w : B.Obj) (r : ℕ)
    (h : RawON C B x b q a b r) (v : (x ⟶[SSet] x).obj q)
    (k : (b ⟶[SSet] w).obj q) : RawON C B x b q a w (r + 1) :=
  ⟨h.1, Fin.snoc h.2.1 h.2.2.2, Fin.snoc h.2.2.1 v, k⟩

def extendNO (q : SimplexCategoryᵒᵖ) (z : B.Obj) (d : C.Obj) (r : ℕ)
    (h : RawNO C B x b q z x r) (u : (b ⟶[SSet] b).obj q)
    (k : (x ⟶[SSet] d).obj q) : RawNO C B x b q z d (r + 1) :=
  ⟨h.1, Fin.snoc h.2.1 h.2.2.2, Fin.snoc h.2.2.1 u, k⟩

def extendNN (q : SimplexCategoryᵒᵖ) (z w : B.Obj) : (r : ℕ) →
    RawNN C B x b q z b r → (x ⟶[SSet] x).obj q →
      (b ⟶[SSet] w).obj q → RawNN C B x b q z w (r + 1)
  | 0, h, v, k => ⟨h, fun _ ↦ v, Fin.elim0, k⟩
  | _ + 1, h, v, k => ⟨h.1, Fin.snoc h.2.1 v, Fin.snoc h.2.2.1 h.2.2.2, k⟩

theorem encode_bLoop (q : SimplexCategoryᵒᵖ) (u : (b ⟶[SSet] b).obj q) :
    encode C B x b (bLoop C B x b q u) = [tag C B q true u] := by
  simp [bLoop, encode_castPath]

theorem encode_bStart (q : SimplexCategoryᵒᵖ) {z : B.Obj}
    (s : (z ⟶[SSet] b).obj q) :
    encode C B x b (bStart C B x b q s) = [tag C B q true s] := by
  simp [bStart, encode_castPath]

theorem encode_bEnd (q : SimplexCategoryᵒᵖ) {w : B.Obj}
    (t : (b ⟶[SSet] w).obj q) :
    encode C B x b (bEnd C B x b q t) = [tag C B q true t] := by
  simp [bEnd, encode_castPath]

theorem encode_extendOO (q : SimplexCategoryᵒᵖ) (a d : C.Obj) (r : ℕ)
    (h : RawOO C B x b q a x r) (u : (b ⟶[SSet] b).obj q)
    (k : (x ⟶[SSet] d).obj q) :
    encode C B x b (decodeOO C B x b q a d (r + 1) (extendOO C B x b q a d r h u k)) =
      [tag C B q false k, tag C B q true u] ++
        encode C B x b (decodeOO C B x b q a x r h) := by
  cases r with
  | zero => simp [extendOO, decodeOO, zig, encode_comp, encode_bLoop]
  | succ n =>
    simp [extendOO, decodeOO, zig, encode_comp, encode_bLoop]

theorem encode_extendON (q : SimplexCategoryᵒᵖ) (a : C.Obj) (w : B.Obj) (r : ℕ)
    (h : RawON C B x b q a b r) (v : (x ⟶[SSet] x).obj q)
    (k : (b ⟶[SSet] w).obj q) :
    encode C B x b (decodeON C B x b q a w (r + 1) (extendON C B x b q a w r h v k)) =
      [tag C B q true k, tag C B q false v] ++
        encode C B x b (decodeON C B x b q a b r h) := by
  simp [extendON, decodeON, zig, encode_comp, encode_bLoop, encode_bEnd]

theorem encode_extendNO (q : SimplexCategoryᵒᵖ) (z : B.Obj) (d : C.Obj) (r : ℕ)
    (h : RawNO C B x b q z x r) (u : (b ⟶[SSet] b).obj q)
    (k : (x ⟶[SSet] d).obj q) :
    encode C B x b (decodeNO C B x b q z d (r + 1) (extendNO C B x b q z d r h u k)) =
      [tag C B q false k, tag C B q true u] ++
        encode C B x b (decodeNO C B x b q z x r h) := by
  simp [extendNO, decodeNO, zag, encode_comp, encode_bLoop, encode_bStart]

theorem encode_extendNN (q : SimplexCategoryᵒᵖ) (z w : B.Obj) (r : ℕ)
    (h : RawNN C B x b q z b r) (v : (x ⟶[SSet] x).obj q)
    (k : (b ⟶[SSet] w).obj q) :
    encode C B x b (decodeNN C B x b q z w (r + 1) (extendNN C B x b q z w r h v k)) =
      [tag C B q true k, tag C B q false v] ++
        encode C B x b (decodeNN C B x b q z b r h) := by
  cases r with
  | zero => simp [extendNN, decodeNN, zag, encode_comp, encode_bStart, encode_bEnd]
  | succ n =>
    simp [extendNN, decodeNN, zag, encode_comp, encode_bStart, encode_bLoop,
      encode_bEnd]

end
end DaggerAmalgamPaddedClassifier
