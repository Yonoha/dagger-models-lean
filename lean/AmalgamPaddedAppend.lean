import AmalgamPaddedRecursion

/-! Single-edge extension of the four literal raw families.
The Boolean packaging only selects their original dependent endpoint types. -/

open CategoryTheory DaggerModels DaggerAmalgamPresentation DaggerAmalgamReduction
open DaggerAmalgamPaddedClassification

universe u

namespace DaggerAmalgamPaddedClassifier
noncomputable section
set_option autoImplicit false
variable (C B : SimplicialCat.{u, u}) (x : C.Obj) (b : B.Obj)

def glueAt (q : SimplexCategoryᵒᵖ) : (c : Bool) → At C B q c
  | false => x
  | true => b

def RawFamily (q : SimplexCategoryᵒᵖ) : (c d : Bool) →
    At C B q c → At C B q d → ℕ → Type u
  | false, false => RawOO C B x b q
  | false, true => RawON C B x b q
  | true, false => RawNO C B x b q
  | true, true => RawNN C B x b q

def decodeFamily (q : SimplexCategoryᵒᵖ) : (c d : Bool) →
    (a : At C B q c) → (z : At C B q d) → (r : ℕ) → RawFamily C B x b q c d a z r →
      Path C B x b q (label C B x b c a) (label C B x b d z)
  | false, false => decodeOO C B x b q
  | false, true => decodeON C B x b q
  | true, false => decodeNO C B x b q
  | true, true => decodeNN C B x b q

def appendOOtoON (q : SimplexCategoryᵒᵖ) (a : C.Obj) (w : B.Obj) : (r : ℕ) →
    RawOO C B x b q a x r → (b ⟶[SSet] w).obj q → RawON C B x b q a w r
  | 0, h, k => ⟨h, Fin.elim0, Fin.elim0, k⟩
  | _ + 1, h, k => ⟨h.1, h.2.1, Fin.snoc h.2.2.1 h.2.2.2, k⟩

def appendONtoOO (q : SimplexCategoryᵒᵖ) (a d : C.Obj) (r : ℕ)
    (h : RawON C B x b q a b r) (k : (x ⟶[SSet] d).obj q) :
    RawOO C B x b q a d (r + 1) := ⟨h.1, Fin.snoc h.2.1 h.2.2.2, h.2.2.1, k⟩

def appendNOtoNN (q : SimplexCategoryᵒᵖ) (z w : B.Obj) (r : ℕ)
    (h : RawNO C B x b q z x r) (k : (b ⟶[SSet] w).obj q) :
    RawNN C B x b q z w (r + 1) := ⟨h.1, Fin.snoc h.2.1 h.2.2.2, h.2.2.1, k⟩

def appendNNtoNO (q : SimplexCategoryᵒᵖ) (z : B.Obj) (d : C.Obj) : (r : ℕ) →
    RawNN C B x b q z b r → (x ⟶[SSet] d).obj q → RawNO C B x b q z d r
  | 0, h, k => ⟨h, Fin.elim0, Fin.elim0, k⟩
  | _ + 1, h, k => ⟨h.1, h.2.1, Fin.snoc h.2.2.1 h.2.2.2, k⟩

def appendFamily (q : SimplexCategoryᵒᵖ) : (c d : Bool) →
    (a : At C B q c) → (z : At C B q d) →
      (Σ r, RawFamily C B x b q c (!d) a (glueAt C B x b q (!d)) r) →
        (glueAt C B x b q d ⟶ z) → Σ r, RawFamily C B x b q c d a z r
  | false, false, a, z, ⟨r, h⟩, k => ⟨r + 1, appendONtoOO C B x b q a z r h k⟩
  | false, true, a, z, ⟨r, h⟩, k => ⟨r, appendOOtoON C B x b q a z r h k⟩
  | true, false, a, z, ⟨r, h⟩, k => ⟨r, appendNNtoNO C B x b q a z r h k⟩
  | true, true, a, z, ⟨r, h⟩, k => ⟨r + 1, appendNOtoNN C B x b q a z r h k⟩

theorem encode_appendFamily (q : SimplexCategoryᵒᵖ) (c d : Bool)
    (a : At C B q c) (z : At C B q d)
    (h : Σ r, RawFamily C B x b q c (!d) a (glueAt C B x b q (!d)) r)
    (k : glueAt C B x b q d ⟶ z) :
    encode C B x b (decodeFamily C B x b q c d a z
      (appendFamily C B x b q c d a z h k).1 (appendFamily C B x b q c d a z h k).2) =
        tag C B q d k :: encode C B x b
          (decodeFamily C B x b q c (!d) a (glueAt C B x b q (!d)) h.1 h.2) := by
  rcases h with ⟨r, h⟩
  cases c <;> cases d <;> cases r <;>
    simp [Bool.not, glueAt, appendFamily, appendOOtoON, appendONtoOO, appendNNtoNO, appendNOtoNN,
      decodeFamily, decodeOO, decodeON, decodeNO, decodeNN, zig, zag,
      encode_comp, encode_bLoop, encode_bStart, encode_bEnd]
  all_goals exact congrArg (tag C B q _) (Fin.snoc_last _ _)

end
end DaggerAmalgamPaddedClassifier
