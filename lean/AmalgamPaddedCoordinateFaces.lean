import AmalgamPaddedIndexedFaces

/-! Full chosen face data at EVERY original critical unit coordinate, not just one face. -/

open CategoryTheory DaggerModels DaggerAmalgamPresentation DaggerAmalgamReduction
open DaggerAmalgamPaddedClassification DaggerAmalgamNormalForms DaggerAmalgamPathMeasure

universe u
namespace DaggerAmalgamPaddedClassifier
noncomputable section
set_option autoImplicit false
variable (C B : SimplicialCat.{u, u}) (x : C.Obj) (b : B.Obj)

def indexedFaceOO_B (q : SimplexCategoryᵒᵖ) (a d : C.Obj) (n : ℕ)
    (h : RawOO C B x b q a d (n + 1)) (i : Fin (n + 1))
    (hi : h.2.1 i = (eId SSet b).app q PUnit.unit) :
    IndexedUnitFaceData C B x b (2 * (n - i.val) + 1) (decodeOO C B x b q a d (n + 1) h)
      (tag C B q true (h.2.1 i)) :=
  indexedUnitFace C B x b (2 * (n - i.val) + 1) _ _ (alternating_decodeOO C B x b q a d (n + 1) h)
    ((identity_Bloop_iff C B b q _).2 hi)
    (slotOO_B C B x b q a d n h i)

def faceOO_B (q : SimplexCategoryᵒᵖ) (a d : C.Obj) (n : ℕ)
    (h : RawOO C B x b q a d (n + 1)) (i : Fin (n + 1))
    (hi : h.2.1 i = (eId SSet b).app q PUnit.unit) :
    UnitFaceData C B x b (decodeOO C B x b q a d (n + 1) h)
      (tag C B q true (h.2.1 i)) :=
  (indexedFaceOO_B C B x b q a d n h i hi).toUnitFaceData

theorem faceOO_B_position (q : SimplexCategoryᵒᵖ) (a d : C.Obj) (n : ℕ)
    (h : RawOO C B x b q a d (n + 1)) (i : Fin (n + 1))
    (hi : h.2.1 i = (eId SSet b).app q PUnit.unit) :
    (faceOO_B C B x b q a d n h i hi).pre.length + 1 = 2 * (n - i.val) + 1 :=
  (indexedFaceOO_B C B x b q a d n h i hi).position

def indexedFaceOO_C (q : SimplexCategoryᵒᵖ) (a d : C.Obj) (n : ℕ)
    (h : RawOO C B x b q a d (n + 1)) (i : Fin n)
    (hi : h.2.2.1 i = (eId SSet x).app q PUnit.unit) :
    IndexedUnitFaceData C B x b (2 * (n - 1 - i.val) + 2) (decodeOO C B x b q a d (n + 1) h)
      (tag C B q false (h.2.2.1 i)) :=
  indexedUnitFace C B x b (2 * (n - 1 - i.val) + 2) _ _ (alternating_decodeOO C B x b q a d (n
      + 1) h)
    ((identity_Cloop_iff C B x q _).2 hi)
    (slotOO_C C B x b q a d n h i)

def faceOO_C (q : SimplexCategoryᵒᵖ) (a d : C.Obj) (n : ℕ)
    (h : RawOO C B x b q a d (n + 1)) (i : Fin n)
    (hi : h.2.2.1 i = (eId SSet x).app q PUnit.unit) :
    UnitFaceData C B x b (decodeOO C B x b q a d (n + 1) h)
      (tag C B q false (h.2.2.1 i)) :=
  (indexedFaceOO_C C B x b q a d n h i hi).toUnitFaceData

theorem faceOO_C_position (q : SimplexCategoryᵒᵖ) (a d : C.Obj) (n : ℕ)
    (h : RawOO C B x b q a d (n + 1)) (i : Fin n)
    (hi : h.2.2.1 i = (eId SSet x).app q PUnit.unit) :
    (faceOO_C C B x b q a d n h i hi).pre.length + 1 = 2 * (n - 1 - i.val) + 2 :=
  (indexedFaceOO_C C B x b q a d n h i hi).position

def indexedFaceON_B (q : SimplexCategoryᵒᵖ) (a : C.Obj) (w : B.Obj) (n : ℕ)
    (h : RawON C B x b q a w n) (i : Fin n)
    (hi : h.2.1 i = (eId SSet b).app q PUnit.unit) :
    IndexedUnitFaceData C B x b (2 * (n - 1 - i.val) + 2) (decodeON C B x b q a w n h)
      (tag C B q true (h.2.1 i)) :=
  indexedUnitFace C B x b (2 * (n - 1 - i.val) + 2) _ _ (alternating_decodeON C B x b q a w n h)
    ((identity_Bloop_iff C B b q _).2 hi)
    (slotON_B C B x b q a w n h i)

def faceON_B (q : SimplexCategoryᵒᵖ) (a : C.Obj) (w : B.Obj) (n : ℕ)
    (h : RawON C B x b q a w n) (i : Fin n)
    (hi : h.2.1 i = (eId SSet b).app q PUnit.unit) :
    UnitFaceData C B x b (decodeON C B x b q a w n h)
      (tag C B q true (h.2.1 i)) :=
  (indexedFaceON_B C B x b q a w n h i hi).toUnitFaceData

theorem faceON_B_position (q : SimplexCategoryᵒᵖ) (a : C.Obj) (w : B.Obj) (n : ℕ)
    (h : RawON C B x b q a w n) (i : Fin n)
    (hi : h.2.1 i = (eId SSet b).app q PUnit.unit) :
    (faceON_B C B x b q a w n h i hi).pre.length + 1 = 2 * (n - 1 - i.val) + 2 :=
  (indexedFaceON_B C B x b q a w n h i hi).position

def indexedFaceON_C (q : SimplexCategoryᵒᵖ) (a : C.Obj) (w : B.Obj) (n : ℕ)
    (h : RawON C B x b q a w n) (i : Fin n)
    (hi : h.2.2.1 i = (eId SSet x).app q PUnit.unit) :
    IndexedUnitFaceData C B x b (2 * (n - 1 - i.val) + 1) (decodeON C B x b q a w n h)
      (tag C B q false (h.2.2.1 i)) :=
  indexedUnitFace C B x b (2 * (n - 1 - i.val) + 1) _ _ (alternating_decodeON C B x b q a w n h)
    ((identity_Cloop_iff C B x q _).2 hi)
    (slotON_C C B x b q a w n h i)

def faceON_C (q : SimplexCategoryᵒᵖ) (a : C.Obj) (w : B.Obj) (n : ℕ)
    (h : RawON C B x b q a w n) (i : Fin n)
    (hi : h.2.2.1 i = (eId SSet x).app q PUnit.unit) :
    UnitFaceData C B x b (decodeON C B x b q a w n h)
      (tag C B q false (h.2.2.1 i)) :=
  (indexedFaceON_C C B x b q a w n h i hi).toUnitFaceData

theorem faceON_C_position (q : SimplexCategoryᵒᵖ) (a : C.Obj) (w : B.Obj) (n : ℕ)
    (h : RawON C B x b q a w n) (i : Fin n)
    (hi : h.2.2.1 i = (eId SSet x).app q PUnit.unit) :
    (faceON_C C B x b q a w n h i hi).pre.length + 1 = 2 * (n - 1 - i.val) + 1 :=
  (indexedFaceON_C C B x b q a w n h i hi).position

def indexedFaceNO_C (q : SimplexCategoryᵒᵖ) (z : B.Obj) (d : C.Obj) (n : ℕ)
    (h : RawNO C B x b q z d n) (i : Fin n)
    (hi : h.2.1 i = (eId SSet x).app q PUnit.unit) :
    IndexedUnitFaceData C B x b (2 * (n - 1 - i.val) + 2) (decodeNO C B x b q z d n h)
      (tag C B q false (h.2.1 i)) :=
  indexedUnitFace C B x b (2 * (n - 1 - i.val) + 2) _ _ (alternating_decodeNO C B x b q z d n h)
    ((identity_Cloop_iff C B x q _).2 hi)
    (slotNO_C C B x b q z d n h i)

def faceNO_C (q : SimplexCategoryᵒᵖ) (z : B.Obj) (d : C.Obj) (n : ℕ)
    (h : RawNO C B x b q z d n) (i : Fin n)
    (hi : h.2.1 i = (eId SSet x).app q PUnit.unit) :
    UnitFaceData C B x b (decodeNO C B x b q z d n h)
      (tag C B q false (h.2.1 i)) :=
  (indexedFaceNO_C C B x b q z d n h i hi).toUnitFaceData

theorem faceNO_C_position (q : SimplexCategoryᵒᵖ) (z : B.Obj) (d : C.Obj) (n : ℕ)
    (h : RawNO C B x b q z d n) (i : Fin n)
    (hi : h.2.1 i = (eId SSet x).app q PUnit.unit) :
    (faceNO_C C B x b q z d n h i hi).pre.length + 1 = 2 * (n - 1 - i.val) + 2 :=
  (indexedFaceNO_C C B x b q z d n h i hi).position

def indexedFaceNO_B (q : SimplexCategoryᵒᵖ) (z : B.Obj) (d : C.Obj) (n : ℕ)
    (h : RawNO C B x b q z d n) (i : Fin n)
    (hi : h.2.2.1 i = (eId SSet b).app q PUnit.unit) :
    IndexedUnitFaceData C B x b (2 * (n - 1 - i.val) + 1) (decodeNO C B x b q z d n h)
      (tag C B q true (h.2.2.1 i)) :=
  indexedUnitFace C B x b (2 * (n - 1 - i.val) + 1) _ _ (alternating_decodeNO C B x b q z d n h)
    ((identity_Bloop_iff C B b q _).2 hi)
    (slotNO_B C B x b q z d n h i)

def faceNO_B (q : SimplexCategoryᵒᵖ) (z : B.Obj) (d : C.Obj) (n : ℕ)
    (h : RawNO C B x b q z d n) (i : Fin n)
    (hi : h.2.2.1 i = (eId SSet b).app q PUnit.unit) :
    UnitFaceData C B x b (decodeNO C B x b q z d n h)
      (tag C B q true (h.2.2.1 i)) :=
  (indexedFaceNO_B C B x b q z d n h i hi).toUnitFaceData

theorem faceNO_B_position (q : SimplexCategoryᵒᵖ) (z : B.Obj) (d : C.Obj) (n : ℕ)
    (h : RawNO C B x b q z d n) (i : Fin n)
    (hi : h.2.2.1 i = (eId SSet b).app q PUnit.unit) :
    (faceNO_B C B x b q z d n h i hi).pre.length + 1 = 2 * (n - 1 - i.val) + 1 :=
  (indexedFaceNO_B C B x b q z d n h i hi).position

def indexedFaceNN_C (q : SimplexCategoryᵒᵖ) (z w : B.Obj) (n : ℕ)
    (h : RawNN C B x b q z w (n + 1)) (i : Fin (n + 1))
    (hi : h.2.1 i = (eId SSet x).app q PUnit.unit) :
    IndexedUnitFaceData C B x b (2 * (n - i.val) + 1) (decodeNN C B x b q z w (n + 1) h)
      (tag C B q false (h.2.1 i)) :=
  indexedUnitFace C B x b (2 * (n - i.val) + 1) _ _ (alternating_decodeNN C B x b q z w (n + 1) h)
    ((identity_Cloop_iff C B x q _).2 hi)
    (slotNN_C C B x b q z w n h i)

def faceNN_C (q : SimplexCategoryᵒᵖ) (z w : B.Obj) (n : ℕ)
    (h : RawNN C B x b q z w (n + 1)) (i : Fin (n + 1))
    (hi : h.2.1 i = (eId SSet x).app q PUnit.unit) :
    UnitFaceData C B x b (decodeNN C B x b q z w (n + 1) h)
      (tag C B q false (h.2.1 i)) :=
  (indexedFaceNN_C C B x b q z w n h i hi).toUnitFaceData

theorem faceNN_C_position (q : SimplexCategoryᵒᵖ) (z w : B.Obj) (n : ℕ)
    (h : RawNN C B x b q z w (n + 1)) (i : Fin (n + 1))
    (hi : h.2.1 i = (eId SSet x).app q PUnit.unit) :
    (faceNN_C C B x b q z w n h i hi).pre.length + 1 = 2 * (n - i.val) + 1 :=
  (indexedFaceNN_C C B x b q z w n h i hi).position

def indexedFaceNN_B (q : SimplexCategoryᵒᵖ) (z w : B.Obj) (n : ℕ)
    (h : RawNN C B x b q z w (n + 1)) (i : Fin n)
    (hi : h.2.2.1 i = (eId SSet b).app q PUnit.unit) :
    IndexedUnitFaceData C B x b (2 * (n - 1 - i.val) + 2) (decodeNN C B x b q z w (n + 1) h)
      (tag C B q true (h.2.2.1 i)) :=
  indexedUnitFace C B x b (2 * (n - 1 - i.val) + 2) _ _ (alternating_decodeNN C B x b q z w (n
      + 1) h)
    ((identity_Bloop_iff C B b q _).2 hi)
    (slotNN_B C B x b q z w n h i)

def faceNN_B (q : SimplexCategoryᵒᵖ) (z w : B.Obj) (n : ℕ)
    (h : RawNN C B x b q z w (n + 1)) (i : Fin n)
    (hi : h.2.2.1 i = (eId SSet b).app q PUnit.unit) :
    UnitFaceData C B x b (decodeNN C B x b q z w (n + 1) h)
      (tag C B q true (h.2.2.1 i)) :=
  (indexedFaceNN_B C B x b q z w n h i hi).toUnitFaceData

theorem faceNN_B_position (q : SimplexCategoryᵒᵖ) (z w : B.Obj) (n : ℕ)
    (h : RawNN C B x b q z w (n + 1)) (i : Fin n)
    (hi : h.2.2.1 i = (eId SSet b).app q PUnit.unit) :
    (faceNN_B C B x b q z w n h i hi).pre.length + 1 = 2 * (n - 1 - i.val) + 2 :=
  (indexedFaceNN_B C B x b q z w n h i hi).position

def UnitFaceData.slotOfPosition {q : SimplexCategoryᵒᵖ} {s t : Objects C B x b}
    {p : Path C B x b q s t} {unit : Edge C B q} (fd : UnitFaceData C B x b p unit)
    (k : ℕ) (hp : fd.pre.length + 1 = k) :
    SlotOccurrence C B k unit (encode C B x b p) :=
  ⟨fd.pre, fd.left, fd.right, fd.post, fd.original_encode, hp⟩

end
end DaggerAmalgamPaddedClassifier
