import AmalgamPaddedStages

/-! Every original simplex operator acts on all tuple coordinates, then actual normalization. -/

open CategoryTheory DaggerModels DaggerAmalgamPresentation
open DaggerAmalgamPaddedClassification DaggerAmalgamNormalForms

universe u
namespace DaggerAmalgamPaddedClassifier
noncomputable section
set_option autoImplicit false
variable (C B : SimplicialCat.{u, u}) (x : C.Obj) (b : B.Obj)

theorem map_castPath {q q' : SimplexCategoryᵒᵖ} (α : q ⟶ q')
    {s t s' t' : Objects C B x b} (hs : s = s') (ht : t = t')
    (p : Path C B x b q s t) :
    SimplicialColimitsFree.Paths.map (graph C B x b) α (castPath C B x b hs ht p) =
      castPath C B x b hs ht (SimplicialColimitsFree.Paths.map (graph C B x b) α p) := by
  cases hs
  cases ht
  rfl

theorem map_bLoop {q q' : SimplexCategoryᵒᵖ} (α : q ⟶ q')
    (h : (b ⟶[SSet] b).obj q) :
    SimplicialColimitsFree.Paths.map (graph C B x b) α (bLoop C B x b q h) =
      bLoop C B x b q' ((b ⟶[SSet] b).map α h) := by
  simp only [bLoop, map_castPath, map_factorPath]

theorem map_bStart {q q' : SimplexCategoryᵒᵖ} (α : q ⟶ q') {z : B.Obj}
    (h : (z ⟶[SSet] b).obj q) :
    SimplicialColimitsFree.Paths.map (graph C B x b) α (bStart C B x b q h) =
      bStart C B x b q' ((z ⟶[SSet] b).map α h) := by
  simp only [bStart, map_castPath, map_factorPath]

theorem map_bEnd {q q' : SimplexCategoryᵒᵖ} (α : q ⟶ q') {w : B.Obj}
    (h : (b ⟶[SSet] w).obj q) :
    SimplicialColimitsFree.Paths.map (graph C B x b) α (bEnd C B x b q h) =
      bEnd C B x b q' ((b ⟶[SSet] w).map α h) := by
  simp only [bEnd, map_castPath, map_factorPath]

theorem map_zig {q q' : SimplexCategoryᵒᵖ} (α : q ⟶ q') : ∀ n us vs,
    SimplicialColimitsFree.Paths.map (graph C B x b) α (zig C B x b q n us vs) =
      zig C B x b q' n (fun i ↦ (b ⟶[SSet] b).map α (us i))
        (fun i ↦ (x ⟶[SSet] x).map α (vs i)) := by
  intro n
  induction n with
  | zero => intro us vs; rfl
  | succ n ih => intro us vs; simp only [zig, SimplicialColimitsFree.Paths.map_pathComp,
      map_bLoop, map_factorPath, ih]

theorem map_zag {q q' : SimplexCategoryᵒᵖ} (α : q ⟶ q') : ∀ n vs us,
    SimplicialColimitsFree.Paths.map (graph C B x b) α (zag C B x b q n vs us) =
      zag C B x b q' n (fun i ↦ (x ⟶[SSet] x).map α (vs i))
        (fun i ↦ (b ⟶[SSet] b).map α (us i)) := by
  intro n
  induction n with
  | zero => intro vs us; rfl
  | succ n ih => intro vs us; simp only [zag, SimplicialColimitsFree.Paths.map_pathComp,
      map_bLoop, map_factorPath, ih]

def mapRawOO {q q' : SimplexCategoryᵒᵖ} (α : q ⟶ q') (a d : C.Obj) :
    (r : ℕ) → RawOO C B x b q a d r → RawOO C B x b q' a d r
  | 0, h => (a ⟶[SSet] d).map α h
  | _ + 1, h => ⟨(a ⟶[SSet] x).map α h.1, (fun i ↦ (b ⟶[SSet] b).map α (h.2.1 i)),
      (fun i ↦ (x ⟶[SSet] x).map α (h.2.2.1 i)), (x ⟶[SSet] d).map α h.2.2.2⟩

def mapRawON {q q' : SimplexCategoryᵒᵖ} (α : q ⟶ q') (a : C.Obj) (w : B.Obj) (r : ℕ)
    (h : RawON C B x b q a w r) : RawON C B x b q' a w r :=
  ⟨(a ⟶[SSet] x).map α h.1, (fun i ↦ (b ⟶[SSet] b).map α (h.2.1 i)),
    (fun i ↦ (x ⟶[SSet] x).map α (h.2.2.1 i)), (b ⟶[SSet] w).map α h.2.2.2⟩

def mapRawNO {q q' : SimplexCategoryᵒᵖ} (α : q ⟶ q') (z : B.Obj) (d : C.Obj) (r : ℕ)
    (h : RawNO C B x b q z d r) : RawNO C B x b q' z d r :=
  ⟨(z ⟶[SSet] b).map α h.1, (fun i ↦ (x ⟶[SSet] x).map α (h.2.1 i)),
    (fun i ↦ (b ⟶[SSet] b).map α (h.2.2.1 i)), (x ⟶[SSet] d).map α h.2.2.2⟩

def mapRawNN {q q' : SimplexCategoryᵒᵖ} (α : q ⟶ q') (z w : B.Obj) :
    (r : ℕ) → RawNN C B x b q z w r → RawNN C B x b q' z w r
  | 0, h => (z ⟶[SSet] w).map α h
  | _ + 1, h => ⟨(z ⟶[SSet] b).map α h.1, (fun i ↦ (x ⟶[SSet] x).map α (h.2.1 i)),
      (fun i ↦ (b ⟶[SSet] b).map α (h.2.2.1 i)), (b ⟶[SSet] w).map α h.2.2.2⟩

theorem map_decodeOO {q q' : SimplexCategoryᵒᵖ} (α : q ⟶ q') (a d : C.Obj)
    (r : ℕ) (h : RawOO C B x b q a d r) :
    SimplicialColimitsFree.Paths.map (graph C B x b) α (decodeOO C B x b q a d r h) =
      decodeOO C B x b q' a d r (mapRawOO C B x b α a d r h) := by
  cases r with
  | zero => rfl
  | succ n =>
    simp only [decodeOO, mapRawOO, SimplicialColimitsFree.Paths.map_pathComp,
      map_factorPath, map_bLoop, map_zig]

theorem map_evalOO {q q' : SimplexCategoryᵒᵖ} (α : q ⟶ q') (a d : C.Obj)
    (r : ℕ) (h : RawOO C B x b q a d r) :
    SimplicialCat.HomQuotient.map (relations C B x b) α (evalOO C B x b q a d r h) =
      evalOO C B x b q' a d r (mapRawOO C B x b α a d r h) := by
  simp only [evalOO, SimplicialCat.HomQuotient.map_mk]
  exact congrArg (SimplicialCat.HomQuotient.mk _ q')
    (map_decodeOO C B x b α a d r h)

theorem normalize_operatorOO {q q' : SimplexCategoryᵒᵖ} (α : q ⟶ q') (a d : C.Obj)
    (r : ℕ) (h : RawOO C B x b q a d r) :
    normalize C B x b (decodeOO C B x b q' a d r (mapRawOO C B x b α a d r h)) =
      DaggerAmalgamNormalForms.map C B x b α
        (normalize C B x b (decodeOO C B x b q a d r h)) := by
  rw [← map_decodeOO]
  exact (normalize_raw_map C B x b α _).symm

theorem map_decodeON {q q' : SimplexCategoryᵒᵖ} (α : q ⟶ q') (a : C.Obj) (w : B.Obj)
    (r : ℕ) (h : RawON C B x b q a w r) :
    SimplicialColimitsFree.Paths.map (graph C B x b) α (decodeON C B x b q a w r h) =
      decodeON C B x b q' a w r (mapRawON C B x b α a w r h) := by
  simp only [decodeON, mapRawON, SimplicialColimitsFree.Paths.map_pathComp,
      map_factorPath, map_bEnd, map_zig]

theorem map_evalON {q q' : SimplexCategoryᵒᵖ} (α : q ⟶ q') (a : C.Obj) (w : B.Obj)
    (r : ℕ) (h : RawON C B x b q a w r) :
    SimplicialCat.HomQuotient.map (relations C B x b) α (evalON C B x b q a w r h) =
      evalON C B x b q' a w r (mapRawON C B x b α a w r h) := by
  simp only [evalON, SimplicialCat.HomQuotient.map_mk]
  exact congrArg (SimplicialCat.HomQuotient.mk _ q')
    (map_decodeON C B x b α a w r h)

theorem normalize_operatorON {q q' : SimplexCategoryᵒᵖ} (α : q ⟶ q') (a : C.Obj) (w : B.Obj)
    (r : ℕ) (h : RawON C B x b q a w r) :
    normalize C B x b (decodeON C B x b q' a w r (mapRawON C B x b α a w r h)) =
      DaggerAmalgamNormalForms.map C B x b α
        (normalize C B x b (decodeON C B x b q a w r h)) := by
  rw [← map_decodeON]
  exact (normalize_raw_map C B x b α _).symm

theorem map_decodeNO {q q' : SimplexCategoryᵒᵖ} (α : q ⟶ q') (z : B.Obj) (d : C.Obj)
    (r : ℕ) (h : RawNO C B x b q z d r) :
    SimplicialColimitsFree.Paths.map (graph C B x b) α (decodeNO C B x b q z d r h) =
      decodeNO C B x b q' z d r (mapRawNO C B x b α z d r h) := by
  simp only [decodeNO, mapRawNO, SimplicialColimitsFree.Paths.map_pathComp,
      map_factorPath, map_bStart, map_zag]

theorem map_evalNO {q q' : SimplexCategoryᵒᵖ} (α : q ⟶ q') (z : B.Obj) (d : C.Obj)
    (r : ℕ) (h : RawNO C B x b q z d r) :
    SimplicialCat.HomQuotient.map (relations C B x b) α (evalNO C B x b q z d r h) =
      evalNO C B x b q' z d r (mapRawNO C B x b α z d r h) := by
  simp only [evalNO, SimplicialCat.HomQuotient.map_mk]
  exact congrArg (SimplicialCat.HomQuotient.mk _ q')
    (map_decodeNO C B x b α z d r h)

theorem normalize_operatorNO {q q' : SimplexCategoryᵒᵖ} (α : q ⟶ q') (z : B.Obj) (d : C.Obj)
    (r : ℕ) (h : RawNO C B x b q z d r) :
    normalize C B x b (decodeNO C B x b q' z d r (mapRawNO C B x b α z d r h)) =
      DaggerAmalgamNormalForms.map C B x b α
        (normalize C B x b (decodeNO C B x b q z d r h)) := by
  rw [← map_decodeNO]
  exact (normalize_raw_map C B x b α _).symm

theorem map_decodeNN {q q' : SimplexCategoryᵒᵖ} (α : q ⟶ q') (z w : B.Obj)
    (r : ℕ) (h : RawNN C B x b q z w r) :
    SimplicialColimitsFree.Paths.map (graph C B x b) α (decodeNN C B x b q z w r h) =
      decodeNN C B x b q' z w r (mapRawNN C B x b α z w r h) := by
  cases r with
  | zero => rfl
  | succ n =>
    simp only [decodeNN, mapRawNN, SimplicialColimitsFree.Paths.map_pathComp,
      map_factorPath, map_bStart, map_bEnd, map_zag]

theorem map_evalNN {q q' : SimplexCategoryᵒᵖ} (α : q ⟶ q') (z w : B.Obj)
    (r : ℕ) (h : RawNN C B x b q z w r) :
    SimplicialCat.HomQuotient.map (relations C B x b) α (evalNN C B x b q z w r h) =
      evalNN C B x b q' z w r (mapRawNN C B x b α z w r h) := by
  simp only [evalNN, SimplicialCat.HomQuotient.map_mk]
  exact congrArg (SimplicialCat.HomQuotient.mk _ q')
    (map_decodeNN C B x b α z w r h)

theorem normalize_operatorNN {q q' : SimplexCategoryᵒᵖ} (α : q ⟶ q') (z w : B.Obj)
    (r : ℕ) (h : RawNN C B x b q z w r) :
    normalize C B x b (decodeNN C B x b q' z w r (mapRawNN C B x b α z w r h)) =
      DaggerAmalgamNormalForms.map C B x b α
        (normalize C B x b (decodeNN C B x b q z w r h)) := by
  rw [← map_decodeNN]
  exact (normalize_raw_map C B x b α _).symm

end
end DaggerAmalgamPaddedClassifier
