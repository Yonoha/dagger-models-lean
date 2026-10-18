import AmalgamObjectData
import AmalgamPathMeasure

/-! The four original padded tuple families and their actual dependent path decoders.
Endpoint identity padding is retained. No replacement object graph or color encoding is used. -/

open CategoryTheory MonoidalCategory DaggerModels DaggerAmalgamPresentation

universe u

namespace DaggerAmalgamPaddedClassification

noncomputable section
set_option autoImplicit false

variable (C B : SimplicialCat.{u, u}) (x : C.Obj) (b : B.Obj)

/-- Transport the SAME original path at its two endpoints. -/
def castPath {q : SimplexCategoryᵒᵖ} {s t s' t' : Objects C B x b}
    (hs : s = s') (ht : t = t') (p : Path C B x b q s t) : Path C B x b q s' t' := by
  cases hs
  cases ht
  exact p

@[simp] theorem castPath_rfl {q : SimplexCategoryᵒᵖ} {s t : Objects C B x b}
    (p : Path C B x b q s t) : castPath C B x b rfl rfl p = p := rfl

@[simp] theorem rightCount_castPath {q : SimplexCategoryᵒᵖ}
    {s t s' t' : Objects C B x b} (hs : s = s') (ht : t = t')
    (p : Path C B x b q s t) :
    DaggerAmalgamPathMeasure.rightCount C B x b q (castPath C B x b hs ht p) =
      DaggerAmalgamPathMeasure.rightCount C B x b q p := by
  cases hs
  cases ht
  rfl

/-- The B-loop with both endpoints transported by the original glued equality. -/
def bLoop (q : SimplexCategoryᵒᵖ) (h : (b ⟶[SSet] b).obj q) :
    Path C B x b q (leftObj C B x b x) (leftObj C B x b x) :=
  castPath C B x b (glued C B x b).symm (glued C B x b).symm
    (factorPath C B x b true q h)

/-- The B starting edge keeps its original source; only the glue target is transported. -/
def bStart (q : SimplexCategoryᵒᵖ) {z : B.Obj} (h : (z ⟶[SSet] b).obj q) :
    Path C B x b q (rightObj C B x b z) (leftObj C B x b x) :=
  castPath C B x b rfl (glued C B x b).symm (factorPath C B x b true q h)

/-- The B ending edge keeps its original target; only the glue source is transported. -/
def bEnd (q : SimplexCategoryᵒᵖ) {w : B.Obj} (h : (b ⟶[SSet] w).obj q) :
    Path C B x b q (leftObj C B x b x) (rightObj C B x b w) :=
  castPath C B x b (glued C B x b).symm rfl (factorPath C B x b true q h)

/-- Actual B,C loop pairs, in the original path order. -/
def zig (q : SimplexCategoryᵒᵖ) : (n : ℕ) →
    (Fin n → (b ⟶[SSet] b).obj q) → (Fin n → (x ⟶[SSet] x).obj q) →
      Path C B x b q (leftObj C B x b x) (leftObj C B x b x)
  | 0, _, _ => .nil
  | n + 1, us, vs =>
      ((zig q n (fun i ↦ us i.castSucc) (fun i ↦ vs i.castSucc)).comp
        (bLoop C B x b q (us (Fin.last n)))).comp
          (factorPath C B x b false q (vs (Fin.last n)))

/-- Actual C,B loop pairs, in the original path order. -/
def zag (q : SimplexCategoryᵒᵖ) : (n : ℕ) →
    (Fin n → (x ⟶[SSet] x).obj q) → (Fin n → (b ⟶[SSet] b).obj q) →
      Path C B x b q (leftObj C B x b x) (leftObj C B x b x)
  | 0, _, _ => .nil
  | n + 1, vs, us =>
      ((zag q n (fun i ↦ vs i.castSucc) (fun i ↦ us i.castSucc)).comp
        (factorPath C B x b false q (vs (Fin.last n)))).comp
          (bLoop C B x b q (us (Fin.last n)))

/-- Old–old padded data, retaining the complete original endpoint arrows. -/
def RawOO (q : SimplexCategoryᵒᵖ) (a d : C.Obj) : ℕ → Type u
  | 0 => (a ⟶[SSet] d).obj q
  | n + 1 => (a ⟶[SSet] x).obj q × (Fin (n + 1) → (b ⟶[SSet] b).obj q) ×
      (Fin n → (x ⟶[SSet] x).obj q) × (x ⟶[SSet] d).obj q

/-- Old–new data; the last arrow is the original B(b,w), never a chosen point. -/
abbrev RawON (q : SimplexCategoryᵒᵖ) (a : C.Obj) (w : B.Obj) (n : ℕ) :=
  (a ⟶[SSet] x).obj q × (Fin n → (b ⟶[SSet] b).obj q) ×
    (Fin n → (x ⟶[SSet] x).obj q) × (b ⟶[SSet] w).obj q

/-- New–old data in the actual reversed source-to-target order. -/
abbrev RawNO (q : SimplexCategoryᵒᵖ) (z : B.Obj) (d : C.Obj) (n : ℕ) :=
  (z ⟶[SSet] b).obj q × (Fin n → (x ⟶[SSet] x).obj q) ×
    (Fin n → (b ⟶[SSet] b).obj q) × (x ⟶[SSet] d).obj q

/-- New–new data; rank one has only one critical C-loop and no B-loop. -/
def RawNN (q : SimplexCategoryᵒᵖ) (z w : B.Obj) : ℕ → Type u
  | 0 => (z ⟶[SSet] w).obj q
  | n + 1 => (z ⟶[SSet] b).obj q × (Fin (n + 1) → (x ⟶[SSet] x).obj q) ×
      (Fin n → (b ⟶[SSet] b).obj q) × (b ⟶[SSet] w).obj q

/-- The original old–old path; its base is the actual C singleton, including identities. -/
def decodeOO (q : SimplexCategoryᵒᵖ) (a d : C.Obj) : (n : ℕ) →
    RawOO C B x b q a d n → Path C B x b q (leftObj C B x b a) (leftObj C B x b d)
  | 0, h => factorPath C B x b false q h
  | n + 1, h =>
      (((factorPath C B x b false q h.1).comp
        (zig C B x b q n (fun i ↦ h.2.1 i.castSucc) h.2.2.1)).comp
          (bLoop C B x b q (h.2.1 (Fin.last n)))).comp
            (factorPath C B x b false q h.2.2.2)

/-- The original old–new path, with the complete base pair at n=0. -/
def decodeON (q : SimplexCategoryᵒᵖ) (a : C.Obj) (w : B.Obj) (n : ℕ)
    (h : RawON C B x b q a w n) :
    Path C B x b q (leftObj C B x b a) (rightObj C B x b w) :=
  ((factorPath C B x b false q h.1).comp (zig C B x b q n h.2.1 h.2.2.1)).comp
    (bEnd C B x b q h.2.2.2)

/-- The original new–old path, with the complete base pair at n=0. -/
def decodeNO (q : SimplexCategoryᵒᵖ) (z : B.Obj) (d : C.Obj) (n : ℕ)
    (h : RawNO C B x b q z d n) :
    Path C B x b q (rightObj C B x b z) (leftObj C B x b d) :=
  ((bStart C B x b q h.1).comp (zag C B x b q n h.2.1 h.2.2.1)).comp
    (factorPath C B x b false q h.2.2.2)

/-- The original new–new path; its base is the B singleton, including identities. -/
def decodeNN (q : SimplexCategoryᵒᵖ) (z w : B.Obj) : (n : ℕ) →
    RawNN C B x b q z w n → Path C B x b q (rightObj C B x b z) (rightObj C B x b w)
  | 0, h => factorPath C B x b true q h
  | n + 1, h =>
      (((bStart C B x b q h.1).comp
        (zag C B x b q n (fun i ↦ h.2.1 i.castSucc) h.2.2.1)).comp
          (factorPath C B x b false q (h.2.1 (Fin.last n)))).comp
            (bEnd C B x b q h.2.2.2)

end
end DaggerAmalgamPaddedClassification
