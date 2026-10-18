import AmalgamUnitBoundaryProducts
import AmalgamPaddedRaw

/-! The SAME four grouped Raw families and their critical interior unit boundaries. -/

open CategoryTheory MonoidalCategory CartesianMonoidalCategory HomotopicalAlgebra
open DaggerModels
open scoped SSet.modelCategoryQuillen

universe u
namespace DaggerAmalgamUnitBoundary
noncomputable section
set_option autoImplicit false

variable (C B : SimplicialCat.{u, u}) (x : C.Obj) (b : B.Obj)

/-- No critical coordinates at rank zero; the original C Hom is retained. -/
def familyOO (a d : C.Obj) : ℕ → SSet.{u}
  | 0 => a ⟶[SSet] d
  | n + 1 => grouped (a ⟶[SSet] x) (b ⟶[SSet] b) (x ⟶[SSet] x) (x ⟶[SSet] d)
      (n + 1) n

def familyON (a : C.Obj) (w : B.Obj) (n : ℕ) : SSet.{u} :=
  grouped (a ⟶[SSet] x) (b ⟶[SSet] b) (x ⟶[SSet] x) (b ⟶[SSet] w) n n

def familyNO (z : B.Obj) (d : C.Obj) (n : ℕ) : SSet.{u} :=
  grouped (z ⟶[SSet] b) (x ⟶[SSet] x) (b ⟶[SSet] b) (x ⟶[SSet] d) n n

/-- Rank one has a critical C loop and NO critical B loop. -/
def familyNN (z w : B.Obj) : ℕ → SSet.{u}
  | 0 => z ⟶[SSet] w
  | n + 1 => grouped (z ⟶[SSet] b) (x ⟶[SSet] x) (b ⟶[SSet] b) (b ⟶[SSet] w)
      (n + 1) n

@[simp] theorem familyOO_obj (a d : C.Obj) (n : ℕ) (q : SimplexCategoryᵒᵖ) :
    (familyOO C B x b a d n).obj q =
      DaggerAmalgamPaddedClassification.RawOO C B x b q a d n := by cases n <;> rfl

@[simp] theorem familyON_obj (a : C.Obj) (w : B.Obj) (n : ℕ) (q : SimplexCategoryᵒᵖ) :
    (familyON C B x b a w n).obj q =
      DaggerAmalgamPaddedClassification.RawON C B x b q a w n := rfl

@[simp] theorem familyNO_obj (z : B.Obj) (d : C.Obj) (n : ℕ) (q : SimplexCategoryᵒᵖ) :
    (familyNO C B x b z d n).obj q =
      DaggerAmalgamPaddedClassification.RawNO C B x b q z d n := rfl

@[simp] theorem familyNN_obj (z w : B.Obj) (n : ℕ) (q : SimplexCategoryᵒᵖ) :
    (familyNN C B x b z w n).obj q =
      DaggerAmalgamPaddedClassification.RawNN C B x b q z w n := by cases n <;> rfl

/-- These are literal identity equivalences on the full original grouped tuples. -/
def familyOO_degreeEquiv (a d : C.Obj) (n : ℕ) (q : SimplexCategoryᵒᵖ) :
    (familyOO C B x b a d n).obj q ≃
      DaggerAmalgamPaddedClassification.RawOO C B x b q a d n := by
  cases n <;> exact Equiv.refl _

def familyON_degreeEquiv (a : C.Obj) (w : B.Obj) (n : ℕ) (q : SimplexCategoryᵒᵖ) :
    (familyON C B x b a w n).obj q ≃
      DaggerAmalgamPaddedClassification.RawON C B x b q a w n := Equiv.refl _

def familyNO_degreeEquiv (z : B.Obj) (d : C.Obj) (n : ℕ) (q : SimplexCategoryᵒᵖ) :
    (familyNO C B x b z d n).obj q ≃
      DaggerAmalgamPaddedClassification.RawNO C B x b q z d n := Equiv.refl _

def familyNN_degreeEquiv (z w : B.Obj) (n : ℕ) (q : SimplexCategoryᵒᵖ) :
    (familyNN C B x b z w n).obj q ≃
      DaggerAmalgamPaddedClassification.RawNN C B x b q z w n := by
  cases n <;> exact Equiv.refl _

/-- ALL simplex operators act on every original Hom and every Fin-function coordinate. -/
theorem grouped_map (E X Y F : SSet.{u}) (n m : ℕ)
    {q q' : SimplexCategoryᵒᵖ} (α : q ⟶ q') (v : (grouped E X Y F n m).obj q) :
    (grouped E X Y F n m).map α v =
      (E.map α v.1, ((fun i ↦ X.map α (v.2.1 i)),
        ((fun i ↦ Y.map α (v.2.2.1 i)), F.map α v.2.2.2))) := rfl

def boundaryOO (a d : C.Obj) : (n : ℕ) → (familyOO C B x b a d n).Subcomplex
  | 0 => ⊥
  | n + 1 => criticalBoundary (a ⟶[SSet] x) (eId SSet b) (eId SSet x)
      (x ⟶[SSet] d) (n + 1) n

def boundaryON (a : C.Obj) (w : B.Obj) (n : ℕ) :
    (familyON C B x b a w n).Subcomplex :=
  criticalBoundary (a ⟶[SSet] x) (eId SSet b) (eId SSet x) (b ⟶[SSet] w) n n

def boundaryNO (z : B.Obj) (d : C.Obj) (n : ℕ) :
    (familyNO C B x b z d n).Subcomplex :=
  criticalBoundary (z ⟶[SSet] b) (eId SSet x) (eId SSet b) (x ⟶[SSet] d) n n

def boundaryNN (z w : B.Obj) : (n : ℕ) → (familyNN C B x b z w n).Subcomplex
  | 0 => ⊥
  | n + 1 => criticalBoundary (z ⟶[SSet] b) (eId SSet x) (eId SSet b)
      (b ⟶[SSet] w) (n + 1) n

theorem mem_boundaryOO_succ (a d : C.Obj) (n : ℕ) (q : SimplexCategoryᵒᵖ)
    (v : (familyOO C B x b a d (n + 1)).obj q) :
    v ∈ (boundaryOO C B x b a d (n + 1)).obj q ↔
      (∃ i, v.2.1 i = (eId SSet b).app q PUnit.unit) ∨
        (∃ i, v.2.2.1 i = (eId SSet x).app q PUnit.unit) :=
  mem_criticalBoundary _ _ _ _ _ _ _ _

theorem mem_boundaryON (a : C.Obj) (w : B.Obj) (n : ℕ) (q : SimplexCategoryᵒᵖ)
    (v : (familyON C B x b a w n).obj q) :
    v ∈ (boundaryON C B x b a w n).obj q ↔
      (∃ i, v.2.1 i = (eId SSet b).app q PUnit.unit) ∨
        (∃ i, v.2.2.1 i = (eId SSet x).app q PUnit.unit) :=
  mem_criticalBoundary _ _ _ _ _ _ _ _

theorem mem_boundaryNO (z : B.Obj) (d : C.Obj) (n : ℕ) (q : SimplexCategoryᵒᵖ)
    (v : (familyNO C B x b z d n).obj q) :
    v ∈ (boundaryNO C B x b z d n).obj q ↔
      (∃ i, v.2.1 i = (eId SSet x).app q PUnit.unit) ∨
        (∃ i, v.2.2.1 i = (eId SSet b).app q PUnit.unit) :=
  mem_criticalBoundary _ _ _ _ _ _ _ _

theorem mem_boundaryNN_succ (z w : B.Obj) (n : ℕ) (q : SimplexCategoryᵒᵖ)
    (v : (familyNN C B x b z w (n + 1)).obj q) :
    v ∈ (boundaryNN C B x b z w (n + 1)).obj q ↔
      (∃ i, v.2.1 i = (eId SSet x).app q PUnit.unit) ∨
        (∃ i, v.2.2.1 i = (eId SSet b).app q PUnit.unit) :=
  mem_criticalBoundary _ _ _ _ _ _ _ _

@[simp] theorem boundaryOO_zero (a d : C.Obj) : boundaryOO C B x b a d 0 = ⊥ := rfl
@[simp] theorem boundaryNN_zero (z w : B.Obj) : boundaryNN C B x b z w 0 = ⊥ := rfl
@[simp] theorem boundaryON_zero (a : C.Obj) (w : B.Obj) :
    boundaryON C B x b a w 0 = ⊥ := criticalBoundary_zero _ _ _ _
@[simp] theorem boundaryNO_zero (z : B.Obj) (d : C.Obj) :
    boundaryNO C B x b z d 0 = ⊥ := criticalBoundary_zero _ _ _ _

/-- The exceptional NN1 boundary contains ONLY the original C-loop unit. -/
theorem mem_boundaryNN_one (z w : B.Obj) (q : SimplexCategoryᵒᵖ)
    (v : (familyNN C B x b z w 1).obj q) :
    v ∈ (boundaryNN C B x b z w 1).obj q ↔
      v.2.1 0 = (eId SSet x).app q PUnit.unit := by
  rw [mem_boundaryNN_succ]
  simp

/-- All original boundary inclusions are monomorphisms, including NN1 and rank zero. -/
theorem boundaryOO_mono (a d : C.Obj) (n : ℕ) : Mono (boundaryOO C B x b a d n).ι :=
  inferInstance
theorem boundaryON_mono (a : C.Obj) (w : B.Obj) (n : ℕ) :
    Mono (boundaryON C B x b a w n).ι := inferInstance
theorem boundaryNO_mono (z : B.Obj) (d : C.Obj) (n : ℕ) :
    Mono (boundaryNO C B x b z d n).ι := inferInstance
theorem boundaryNN_mono (z w : B.Obj) (n : ℕ) : Mono (boundaryNN C B x b z w n).ι :=
  inferInstance

/-- The actual OO coordinate faces, with both endpoint Hom factors preserved. -/
def faceOO (a d : C.Obj) (n : ℕ) (S : Set (Fin (n + 1) ⊕ Fin n)) :
    (familyOO C B x b a d (n + 1)).Subcomplex :=
  groupedFace (a ⟶[SSet] x) (eId SSet b) (eId SSet x) (x ⟶[SSet] d) (n + 1) n S

def faceON (a : C.Obj) (w : B.Obj) (n : ℕ) (S : Set (Fin n ⊕ Fin n)) :
    (familyON C B x b a w n).Subcomplex :=
  groupedFace (a ⟶[SSet] x) (eId SSet b) (eId SSet x) (b ⟶[SSet] w) n n S

def faceNO (z : B.Obj) (d : C.Obj) (n : ℕ) (S : Set (Fin n ⊕ Fin n)) :
    (familyNO C B x b z d n).Subcomplex :=
  groupedFace (z ⟶[SSet] b) (eId SSet x) (eId SSet b) (x ⟶[SSet] d) n n S

def faceNN (z w : B.Obj) (n : ℕ) (S : Set (Fin (n + 1) ⊕ Fin n)) :
    (familyNN C B x b z w (n + 1)).Subcomplex :=
  groupedFace (z ⟶[SSet] b) (eId SSet x) (eId SSet b) (b ⟶[SSet] w) (n + 1) n S

/-- The nullary OO/NN intersection is the WHOLE original Hom, not an endpoint product. -/
def faceOOZeroIso (a d : C.Obj) :
    ((⊤ : (familyOO C B x b a d 0).Subcomplex) : SSet.{u}) ≅ (a ⟶[SSet] d) :=
  SSet.Subcomplex.topIso _
def faceNNZeroIso (z w : B.Obj) :
    ((⊤ : (familyNN C B x b z w 0).Subcomplex) : SSet.{u}) ≅ (z ⟶[SSet] w) :=
  SSet.Subcomplex.topIso _

/-- Full face data is the original insertion/forgetting iso, for every subset of coordinates. -/
def faceOOIso (a d : C.Obj) (n : ℕ) (S : Set (Fin (n + 1) ⊕ Fin n)) :
    (faceOO C B x b a d n S : SSet.{u}) ≅
      padded (a ⟶[SSet] x)
        (freeCoordinates (loopCoordinates (b ⟶[SSet] b) (x ⟶[SSet] x) (n + 1) n) S)
          (x ⟶[SSet] d) := groupedFaceIso _ _ _ _ _ _ S

def faceONIso (a : C.Obj) (w : B.Obj) (n : ℕ) (S : Set (Fin n ⊕ Fin n)) :
    (faceON C B x b a w n S : SSet.{u}) ≅
      padded (a ⟶[SSet] x)
        (freeCoordinates (loopCoordinates (b ⟶[SSet] b) (x ⟶[SSet] x) n n) S)
          (b ⟶[SSet] w) := groupedFaceIso _ _ _ _ _ _ S

def faceNOIso (z : B.Obj) (d : C.Obj) (n : ℕ) (S : Set (Fin n ⊕ Fin n)) :
    (faceNO C B x b z d n S : SSet.{u}) ≅
      padded (z ⟶[SSet] b)
        (freeCoordinates (loopCoordinates (x ⟶[SSet] x) (b ⟶[SSet] b) n n) S)
          (x ⟶[SSet] d) := groupedFaceIso _ _ _ _ _ _ S

def faceNNIso (z w : B.Obj) (n : ℕ) (S : Set (Fin (n + 1) ⊕ Fin n)) :
    (faceNN C B x b z w n S : SSet.{u}) ≅
      padded (z ⟶[SSet] b)
        (freeCoordinates (loopCoordinates (x ⟶[SSet] x) (b ⟶[SSet] b) (n + 1) n) S)
          (b ⟶[SSet] w) := groupedFaceIso _ _ _ _ _ _ S

theorem boundaryOO_iSup_faces (a d : C.Obj) (n : ℕ) :
    boundaryOO C B x b a d (n + 1) = ⨆ i, faceOO C B x b a d n {i} :=
  criticalBoundary_iSup_faces _ _ _ _ _ _
theorem boundaryON_iSup_faces (a : C.Obj) (w : B.Obj) (n : ℕ) :
    boundaryON C B x b a w n = ⨆ i, faceON C B x b a w n {i} :=
  criticalBoundary_iSup_faces _ _ _ _ _ _
theorem boundaryNO_iSup_faces (z : B.Obj) (d : C.Obj) (n : ℕ) :
    boundaryNO C B x b z d n = ⨆ i, faceNO C B x b z d n {i} :=
  criticalBoundary_iSup_faces _ _ _ _ _ _
theorem boundaryNN_iSup_faces (z w : B.Obj) (n : ℕ) :
    boundaryNN C B x b z w (n + 1) = ⨆ i, faceNN C B x b z w n {i} :=
  criticalBoundary_iSup_faces _ _ _ _ _ _

variable (hB : SSet.KanComplex.W
  (TopCat.toSSet.map (SSet.toTop.map (toUnit (b ⟶[SSet] b)))))

include hB in
theorem boundaryOO_anodyne (a d : C.Obj) (n : ℕ) :
    SSet.anodyneExtensions (boundaryOO C B x b a d (n + 1)).ι :=
  criticalBoundary_anodyne_left _ _ _ _ (DaggerAmalgamFirstStage.point_anodyne _ hB) n n

include hB in
theorem boundaryON_anodyne (a : C.Obj) (w : B.Obj) (n : ℕ) :
    SSet.anodyneExtensions (boundaryON C B x b a w (n + 1)).ι :=
  criticalBoundary_anodyne_left _ _ _ _ (DaggerAmalgamFirstStage.point_anodyne _ hB) n
    (n + 1)

include hB in
theorem boundaryNO_anodyne (z : B.Obj) (d : C.Obj) (n : ℕ) :
    SSet.anodyneExtensions (boundaryNO C B x b z d (n + 1)).ι :=
  criticalBoundary_anodyne_right _ _ _ _ (DaggerAmalgamFirstStage.point_anodyne _ hB)
    (n + 1) n

include hB in
/-- Exactly rank at least two; no weak-equivalence assertion about NN1. -/
theorem boundaryNN_anodyne (z w : B.Obj) (n : ℕ) :
    SSet.anodyneExtensions (boundaryNN C B x b z w (n + 2)).ι :=
  criticalBoundary_anodyne_right _ _ _ _ (DaggerAmalgamFirstStage.point_anodyne _ hB)
    (n + 2) n

/-- Full original KQ and geometric meanings of the SAME boundary arrow. -/
theorem anodyne_trivial_geometric {X Y : SSet.{u}} (i : X ⟶ Y)
    (hi : SSet.anodyneExtensions i) :
    trivialCofibrations SSet.{u} i ∧
      SSet.KanComplex.W (TopCat.toSSet.map (SSet.toTop.map i)) := by
  have ht := (DaggerOrdinaryAnodyneTensor.anodyne_iff_trivialCofibration i).1 hi
  letI : WeakEquivalence i := ((mem_trivialCofibrations_iff i).1 ht).2
  exact ⟨ht, (DaggerModels.KanQuillenReuse.weakEquivalence_iff_geometric i).1 inferInstance⟩

include hB in
theorem boundaryOO_trivial_geometric (a d : C.Obj) (n : ℕ) :
    trivialCofibrations SSet.{u} (boundaryOO C B x b a d (n + 1)).ι ∧
      SSet.KanComplex.W
        (TopCat.toSSet.map (SSet.toTop.map (boundaryOO C B x b a d (n + 1)).ι)) :=
  anodyne_trivial_geometric _ (boundaryOO_anodyne C B x b hB a d n)

include hB in
theorem boundaryON_trivial_geometric (a : C.Obj) (w : B.Obj) (n : ℕ) :
    trivialCofibrations SSet.{u} (boundaryON C B x b a w (n + 1)).ι ∧
      SSet.KanComplex.W
        (TopCat.toSSet.map (SSet.toTop.map (boundaryON C B x b a w (n + 1)).ι)) :=
  anodyne_trivial_geometric _ (boundaryON_anodyne C B x b hB a w n)

include hB in
theorem boundaryNO_trivial_geometric (z : B.Obj) (d : C.Obj) (n : ℕ) :
    trivialCofibrations SSet.{u} (boundaryNO C B x b z d (n + 1)).ι ∧
      SSet.KanComplex.W
        (TopCat.toSSet.map (SSet.toTop.map (boundaryNO C B x b z d (n + 1)).ι)) :=
  anodyne_trivial_geometric _ (boundaryNO_anodyne C B x b hB z d n)

include hB in
theorem boundaryNN_trivial_geometric (z w : B.Obj) (n : ℕ) :
    trivialCofibrations SSet.{u} (boundaryNN C B x b z w (n + 2)).ι ∧
      SSet.KanComplex.W
        (TopCat.toSSet.map (SSet.toTop.map (boundaryNN C B x b z w (n + 2)).ι)) :=
  anodyne_trivial_geometric _ (boundaryNN_anodyne C B x b hB z w n)

end
end DaggerAmalgamUnitBoundary
