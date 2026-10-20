import AmalgamPaddedRaw

/-! Every original Raw decoder commutes with the same simplicial operator. -/

open CategoryTheory MonoidalCategory DaggerModels DaggerAmalgamPresentation
open DaggerAmalgamPaddedClassification

universe u

set_option autoImplicit false

namespace DaggerAmalgamRawNaturality

noncomputable section

variable (C B : SimplicialCat.{u, u}) (x : C.Obj) (b : B.Obj)
  {q q' : SimplexCategoryᵒᵖ} (α : q ⟶ q')

theorem map_castPath {s t s' t' : Objects C B x b}
    (hs : s = s') (ht : t = t') (p : Path C B x b q s t) :
    SimplicialColimitsFree.Paths.map (graph C B x b) α (castPath C B x b hs ht p) =
    castPath C B x b hs ht (SimplicialColimitsFree.Paths.map (graph C B x b) α p) := by
  cases hs
  cases ht
  rfl

theorem map_bLoop (h : (b ⟶[SSet] b).obj q) :
    SimplicialColimitsFree.Paths.map (graph C B x b) α (bLoop C B x b q h) =
    bLoop C B x b q' ((b ⟶[SSet] b).map α h) := by
  simp only [bLoop, map_castPath, map_factorPath]

theorem map_bStart {z : B.Obj} (h : (z ⟶[SSet] b).obj q) :
    SimplicialColimitsFree.Paths.map (graph C B x b) α (bStart C B x b q h) =
    bStart C B x b q' ((z ⟶[SSet] b).map α h) := by
  simp only [bStart, map_castPath, map_factorPath]

theorem map_bEnd {w : B.Obj} (h : (b ⟶[SSet] w).obj q) :
    SimplicialColimitsFree.Paths.map (graph C B x b) α (bEnd C B x b q h) =
    bEnd C B x b q' ((b ⟶[SSet] w).map α h) := by
  simp only [bEnd, map_castPath, map_factorPath]

theorem map_zig (n : ℕ) (us : Fin n → (b ⟶[SSet] b).obj q)
    (vs : Fin n → (x ⟶[SSet] x).obj q) :
    SimplicialColimitsFree.Paths.map (graph C B x b) α (zig C B x b q n us vs) =
    zig C B x b q' n (fun i ↦ (b ⟶[SSet] b).map α (us i))
      (fun i ↦ (x ⟶[SSet] x).map α (vs i)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [zig, SimplicialColimitsFree.Paths.map_pathComp, ih, map_bLoop, map_factorPath]

theorem map_zag (n : ℕ) (vs : Fin n → (x ⟶[SSet] x).obj q)
    (us : Fin n → (b ⟶[SSet] b).obj q) :
    SimplicialColimitsFree.Paths.map (graph C B x b) α (zag C B x b q n vs us) =
    zag C B x b q' n (fun i ↦ (x ⟶[SSet] x).map α (vs i))
      (fun i ↦ (b ⟶[SSet] b).map α (us i)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [zag, SimplicialColimitsFree.Paths.map_pathComp, ih, map_bLoop, map_factorPath]

def mapOO (a d : C.Obj) : (n : ℕ) → RawOO C B x b q a d n → RawOO C B x b q' a d n
  | 0, h => (a ⟶[SSet] d).map α h
  | _ + 1, h => ((a ⟶[SSet] x).map α h.1,
      (fun i ↦ (b ⟶[SSet] b).map α (h.2.1 i)),
      (fun i ↦ (x ⟶[SSet] x).map α (h.2.2.1 i)), (x ⟶[SSet] d).map α h.2.2.2)

def mapON (a : C.Obj) (w : B.Obj) (n : ℕ) (h : RawON C B x b q a w n) :
    RawON C B x b q' a w n :=
  ((a ⟶[SSet] x).map α h.1, (fun i ↦ (b ⟶[SSet] b).map α (h.2.1 i)),
    (fun i ↦ (x ⟶[SSet] x).map α (h.2.2.1 i)), (b ⟶[SSet] w).map α h.2.2.2)

def mapNO (z : B.Obj) (d : C.Obj) (n : ℕ) (h : RawNO C B x b q z d n) :
    RawNO C B x b q' z d n :=
  ((z ⟶[SSet] b).map α h.1, (fun i ↦ (x ⟶[SSet] x).map α (h.2.1 i)),
    (fun i ↦ (b ⟶[SSet] b).map α (h.2.2.1 i)), (x ⟶[SSet] d).map α h.2.2.2)

def mapNN (z w : B.Obj) : (n : ℕ) → RawNN C B x b q z w n → RawNN C B x b q' z w n
  | 0, h => (z ⟶[SSet] w).map α h
  | _ + 1, h => ((z ⟶[SSet] b).map α h.1,
      (fun i ↦ (x ⟶[SSet] x).map α (h.2.1 i)),
      (fun i ↦ (b ⟶[SSet] b).map α (h.2.2.1 i)), (b ⟶[SSet] w).map α h.2.2.2)

theorem map_decodeOO (a d : C.Obj) (n : ℕ) (h : RawOO C B x b q a d n) :
    SimplicialColimitsFree.Paths.map (graph C B x b) α (decodeOO C B x b q a d n h) =
    decodeOO C B x b q' a d n (mapOO C B x b α a d n h) := by
  cases n with
  | zero => exact map_factorPath C B x b false α h
  | succ n =>
    simp only [decodeOO, mapOO, SimplicialColimitsFree.Paths.map_pathComp,
      map_factorPath, map_zig, map_bLoop]

theorem map_decodeON (a : C.Obj) (w : B.Obj) (n : ℕ) (h : RawON C B x b q a w n) :
    SimplicialColimitsFree.Paths.map (graph C B x b) α (decodeON C B x b q a w n h) =
    decodeON C B x b q' a w n (mapON C B x b α a w n h) := by
  simp only [decodeON, mapON, SimplicialColimitsFree.Paths.map_pathComp,
    map_factorPath, map_zig, map_bEnd]

theorem map_decodeNO (z : B.Obj) (d : C.Obj) (n : ℕ) (h : RawNO C B x b q z d n) :
    SimplicialColimitsFree.Paths.map (graph C B x b) α (decodeNO C B x b q z d n h) =
    decodeNO C B x b q' z d n (mapNO C B x b α z d n h) := by
  simp only [decodeNO, mapNO, SimplicialColimitsFree.Paths.map_pathComp,
    map_factorPath, map_zag, map_bStart]

theorem map_decodeNN (z w : B.Obj) (n : ℕ) (h : RawNN C B x b q z w n) :
    SimplicialColimitsFree.Paths.map (graph C B x b) α (decodeNN C B x b q z w n h) =
    decodeNN C B x b q' z w n (mapNN C B x b α z w n h) := by
  cases n with
  | zero => exact map_factorPath C B x b true α h
  | succ n =>
    simp only [decodeNN, mapNN, SimplicialColimitsFree.Paths.map_pathComp,
      map_factorPath, map_zag, map_bStart, map_bEnd]

/-- The original quotient evaluation, with the same simplex operator on both sides. -/
theorem map_mk_decodeOO (a d : C.Obj) (n : ℕ) (h : RawOO C B x b q a d n) :
    SimplicialCat.HomQuotient.map (relations C B x b) α
      (SimplicialCat.HomQuotient.mk _ q (decodeOO C B x b q a d n h)) =
    SimplicialCat.HomQuotient.mk _ q'
      (decodeOO C B x b q' a d n (mapOO C B x b α a d n h)) := by
  rw [SimplicialCat.HomQuotient.map_mk]
  exact congrArg (SimplicialCat.HomQuotient.mk _ q') (map_decodeOO C B x b α a d n h)

theorem map_mk_decodeON (a : C.Obj) (w : B.Obj) (n : ℕ) (h : RawON C B x b q a w n) :
    SimplicialCat.HomQuotient.map (relations C B x b) α
      (SimplicialCat.HomQuotient.mk _ q (decodeON C B x b q a w n h)) =
    SimplicialCat.HomQuotient.mk _ q'
      (decodeON C B x b q' a w n (mapON C B x b α a w n h)) := by
  rw [SimplicialCat.HomQuotient.map_mk]
  exact congrArg (SimplicialCat.HomQuotient.mk _ q') (map_decodeON C B x b α a w n h)

theorem map_mk_decodeNO (z : B.Obj) (d : C.Obj) (n : ℕ) (h : RawNO C B x b q z d n) :
    SimplicialCat.HomQuotient.map (relations C B x b) α
      (SimplicialCat.HomQuotient.mk _ q (decodeNO C B x b q z d n h)) =
    SimplicialCat.HomQuotient.mk _ q'
      (decodeNO C B x b q' z d n (mapNO C B x b α z d n h)) := by
  rw [SimplicialCat.HomQuotient.map_mk]
  exact congrArg (SimplicialCat.HomQuotient.mk _ q') (map_decodeNO C B x b α z d n h)

theorem map_mk_decodeNN (z w : B.Obj) (n : ℕ) (h : RawNN C B x b q z w n) :
    SimplicialCat.HomQuotient.map (relations C B x b) α
      (SimplicialCat.HomQuotient.mk _ q (decodeNN C B x b q z w n h)) =
    SimplicialCat.HomQuotient.mk _ q'
      (decodeNN C B x b q' z w n (mapNN C B x b α z w n h)) := by
  rw [SimplicialCat.HomQuotient.map_mk]
  exact congrArg (SimplicialCat.HomQuotient.mk _ q') (map_decodeNN C B x b α z w n h)

end
end DaggerAmalgamRawNaturality
