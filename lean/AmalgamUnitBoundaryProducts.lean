import AmalgamFiniteCoordinates

/-! The exact finite critical-coordinate union and endpoint-preserving product transports. -/

open CategoryTheory MonoidalCategory CartesianMonoidalCategory Limits

universe u
namespace DaggerAmalgamUnitBoundary
noncomputable section
set_option autoImplicit false

/-- The union, unlike a face, requires at least ONE critical unit coordinate. -/
def allUnitBoundary {ι : Type} (X : ι → SSet.{u})
    (e : ∀ i, 𝟙_ SSet.{u} ⟶ X i) : (coordinates X).Subcomplex :=
  ⨆ i, (SSet.Subcomplex.range (e i)).preimage (coordinate X i)

theorem mem_allUnitBoundary {ι : Type} (X : ι → SSet.{u})
    (e : ∀ i, 𝟙_ SSet.{u} ⟶ X i) (q : SimplexCategoryᵒᵖ)
    (v : (coordinates X).obj q) :
    v ∈ (allUnitBoundary X e).obj q ↔ ∃ i, v i = (e i).app q PUnit.unit := by
  simp only [allUnitBoundary, SSet.Subcomplex.iSup_obj, Set.mem_iUnion]
  exact exists_congr (fun i ↦ unitRange_mem (e i) q (v i))

def powerBoundary {X : SSet.{u}} (e : 𝟙_ SSet.{u} ⟶ X) (n : ℕ) :
    (finitePower X n).Subcomplex := allUnitBoundary (fun _ : Fin n ↦ X) (fun _ ↦ e)

theorem mem_powerBoundary {X : SSet.{u}} (e : 𝟙_ SSet.{u} ⟶ X) (n : ℕ)
    (q : SimplexCategoryᵒᵖ) (v : (finitePower X n).obj q) :
    v ∈ (powerBoundary e n).obj q ↔ ∃ i, v i = e.app q PUnit.unit :=
  mem_allUnitBoundary _ _ _ _

theorem powerBoundary_zero {X : SSet.{u}} (e : 𝟙_ SSet.{u} ⟶ X) :
    powerBoundary e 0 = ⊥ := by
  ext q v
  rw [mem_powerBoundary]
  simp

theorem powerBoundary_succ_preimage {X : SSet.{u}} (e : 𝟙_ SSet.{u} ⟶ X) (n : ℕ) :
    ((SSet.Subcomplex.range e).unionProd (powerBoundary e n)).preimage
      (powerSuccIso X n).hom = powerBoundary e (n + 1) := by
  ext q v
  change (powerSuccIso X n).hom.app q v ∈
    ((SSet.Subcomplex.range e).unionProd (powerBoundary e n)).obj q ↔ _
  rw [SSet.Subcomplex.mem_unionProd_iff]
  change (v 0 ∈ (SSet.Subcomplex.range e).obj q ∨
    Fin.tail v ∈ (powerBoundary e n).obj q) ↔ _
  rw [unitRange_mem, mem_powerBoundary, mem_powerBoundary]
  constructor
  · rintro (h | ⟨i, h⟩)
    · exact ⟨0, h⟩
    · exact ⟨i.succ, h⟩
  · rintro ⟨i, h⟩
    refine Fin.cases ?_ (fun j ↦ ?_) i h
    · exact Or.inl
    · exact fun h ↦ Or.inr ⟨j, h⟩

def powerBoundarySuccArrowIso {X : SSet.{u}} (e : 𝟙_ SSet.{u} ⟶ X) (n : ℕ) :
    Arrow.mk (powerBoundary e (n + 1)).ι ≅
      Arrow.mk ((SSet.Subcomplex.range e).unionProd (powerBoundary e n)).ι :=
  SSet.Subcomplex.congrArrowι' (powerSuccIso X n) (powerBoundary_succ_preimage e n)

theorem powerBoundary_anodyne {X : SSet.{u}} (e : 𝟙_ SSet.{u} ⟶ X)
    (he : SSet.anodyneExtensions e) (n : ℕ) :
    SSet.anodyneExtensions (powerBoundary e (n + 1)).ι := by
  have hr := (SSet.anodyneExtensions.arrow_mk_iso_iff (unitRangeArrowIso e)).1 he
  exact (SSet.anodyneExtensions.arrow_mk_iso_iff (powerBoundarySuccArrowIso e n)).2
    (SSet.anodyneExtensions.subcomplex_unionProd_mem_of_left _ _ hr)

/-- Exact original endpoint product; its factors are never quotiented or collapsed. -/
def padded (E X F : SSet.{u}) : SSet.{u} := E ⊗ (X ⊗ F)

def paddedBoundary (E : SSet.{u}) {X : SSet.{u}} (A : X.Subcomplex) (F : SSet.{u}) :
    (padded E X F).Subcomplex := (⊤ : E.Subcomplex).prod (A.prod (⊤ : F.Subcomplex))

def paddedBoundaryIso (E : SSet.{u}) {X : SSet.{u}} (A : X.Subcomplex) (F : SSet.{u}) :
    (paddedBoundary E A F : SSet.{u}) ≅ padded E (A : SSet.{u}) F :=
  SSet.Subcomplex.prodIso _ _ ≪≫
    whiskerRightIso (SSet.Subcomplex.topIso E) _ ≪≫
      whiskerLeftIso E (SSet.Subcomplex.prodIso _ _ ≪≫
        whiskerLeftIso _ (SSet.Subcomplex.topIso F))

theorem paddedBoundaryIso_inclusion (E : SSet.{u}) {X : SSet.{u}}
    (A : X.Subcomplex) (F : SSet.{u}) :
    (paddedBoundaryIso E A F).hom ≫ (E ◁ (A.ι ▷ F)) = (paddedBoundary E A F).ι := by
  ext q v <;> rfl

def paddedBoundaryArrowIso (E : SSet.{u}) {X : SSet.{u}}
    (A : X.Subcomplex) (F : SSet.{u}) :
    Arrow.mk (paddedBoundary E A F).ι ≅ Arrow.mk (E ◁ (A.ι ▷ F)) :=
  Arrow.isoMk (paddedBoundaryIso E A F) (Iso.refl _) (by
    simpa using (paddedBoundaryIso_inclusion E A F).symm)

theorem paddedBoundary_anodyne (E : SSet.{u}) {X : SSet.{u}}
    (A : X.Subcomplex) (F : SSet.{u}) (hA : SSet.anodyneExtensions A.ι) :
    SSet.anodyneExtensions (paddedBoundary E A F).ι :=
  (SSet.anodyneExtensions.arrow_mk_iso_iff (paddedBoundaryArrowIso E A F)).2
    (DaggerOrdinaryAnodyneTensor.whiskerLeft _
      (DaggerOrdinaryAnodyneTensor.whiskerRight _ hA F) E)

/-- The SAME grouped coordinates, with only the displayed associator applied. -/
def grouped (E X Y F : SSet.{u}) (n m : ℕ) : SSet.{u} :=
  E ⊗ (finitePower X n ⊗ (finitePower Y m ⊗ F))

def regroupIso (E X Y F : SSet.{u}) (n m : ℕ) :
    grouped E X Y F n m ≅ padded E (finitePower X n ⊗ finitePower Y m) F :=
  whiskerLeftIso E (α_ (finitePower X n) (finitePower Y m) F).symm

@[simp] theorem regroupIso_hom_app (E X Y F : SSet.{u}) (n m : ℕ)
    (q : SimplexCategoryᵒᵖ) (v : (grouped E X Y F n m).obj q) :
    (regroupIso E X Y F n m).hom.app q v = (v.1, ((v.2.1, v.2.2.1), v.2.2.2)) := rfl

@[simp] theorem regroupIso_inv_app (E X Y F : SSet.{u}) (n m : ℕ)
    (q : SimplexCategoryᵒᵖ) (v : (padded E (finitePower X n ⊗ finitePower Y m) F).obj q) :
    (regroupIso E X Y F n m).inv.app q v = (v.1, (v.2.1.1, (v.2.1.2, v.2.2))) := rfl

def criticalBoundary (E : SSet.{u}) {X Y : SSet.{u}}
    (e : 𝟙_ SSet.{u} ⟶ X) (d : 𝟙_ SSet.{u} ⟶ Y) (F : SSet.{u}) (n m : ℕ) :
    (grouped E X Y F n m).Subcomplex :=
  (paddedBoundary E ((powerBoundary e n).unionProd (powerBoundary d m)) F).preimage
    (regroupIso E X Y F n m).hom

theorem mem_criticalBoundary (E : SSet.{u}) {X Y : SSet.{u}}
    (e : 𝟙_ SSet.{u} ⟶ X) (d : 𝟙_ SSet.{u} ⟶ Y) (F : SSet.{u}) (n m : ℕ)
    (q : SimplexCategoryᵒᵖ) (v : (grouped E X Y F n m).obj q) :
    v ∈ (criticalBoundary E e d F n m).obj q ↔
      (∃ i, v.2.1 i = e.app q PUnit.unit) ∨
        (∃ i, v.2.2.1 i = d.app q PUnit.unit) := by
  change (True ∧ _ ∧ True) ↔ _
  simp only [true_and, and_true, SSet.Subcomplex.mem_unionProd_iff,
    mem_powerBoundary]
  rfl

theorem criticalBoundary_zero (E : SSet.{u}) {X Y : SSet.{u}}
    (e : 𝟙_ SSet.{u} ⟶ X) (d : 𝟙_ SSet.{u} ⟶ Y) (F : SSet.{u}) :
    criticalBoundary E e d F 0 0 = ⊥ := by
  ext q v
  rw [mem_criticalBoundary]
  simp

def criticalBoundaryArrowIso (E : SSet.{u}) {X Y : SSet.{u}}
    (e : 𝟙_ SSet.{u} ⟶ X) (d : 𝟙_ SSet.{u} ⟶ Y) (F : SSet.{u}) (n m : ℕ) :
    Arrow.mk (criticalBoundary E e d F n m).ι ≅
      Arrow.mk (E ◁ (((powerBoundary e n).unionProd (powerBoundary d m)).ι ▷ F)) :=
  SSet.Subcomplex.congrArrowι' (regroupIso E X Y F n m) rfl ≪≫
    paddedBoundaryArrowIso E _ F

theorem criticalBoundary_anodyne_left (E : SSet.{u}) {X Y : SSet.{u}}
    (e : 𝟙_ SSet.{u} ⟶ X) (d : 𝟙_ SSet.{u} ⟶ Y) (F : SSet.{u})
    (he : SSet.anodyneExtensions e) (n m : ℕ) :
    SSet.anodyneExtensions (criticalBoundary E e d F (n + 1) m).ι := by
  have h := SSet.anodyneExtensions.subcomplex_unionProd_mem_of_left
    (powerBoundary e (n + 1)) (powerBoundary d m) (powerBoundary_anodyne e he n)
  exact (SSet.anodyneExtensions.arrow_mk_iso_iff
    (criticalBoundaryArrowIso E e d F (n + 1) m)).2
      (DaggerOrdinaryAnodyneTensor.whiskerLeft _
        (DaggerOrdinaryAnodyneTensor.whiskerRight _ h F) E)

theorem criticalBoundary_anodyne_right (E : SSet.{u}) {X Y : SSet.{u}}
    (e : 𝟙_ SSet.{u} ⟶ X) (d : 𝟙_ SSet.{u} ⟶ Y) (F : SSet.{u})
    (hd : SSet.anodyneExtensions d) (n m : ℕ) :
    SSet.anodyneExtensions (criticalBoundary E e d F n (m + 1)).ι := by
  have h := SSet.anodyneExtensions.subcomplex_unionProd_mem_of_right
    (powerBoundary e n) (powerBoundary d (m + 1)) (powerBoundary_anodyne d hd m)
  exact (SSet.anodyneExtensions.arrow_mk_iso_iff
    (criticalBoundaryArrowIso E e d F n (m + 1))).2
      (DaggerOrdinaryAnodyneTensor.whiskerLeft _
        (DaggerOrdinaryAnodyneTensor.whiskerRight _ h F) E)

/-- Heterogeneous loop coordinates preserve both original Fin-function fields. -/
def loopCoordinates (X Y : SSet.{u}) (n m : ℕ) : Fin n ⊕ Fin m → SSet.{u}
  | .inl _ => X
  | .inr _ => Y

def loopUnits {X Y : SSet.{u}} (e : 𝟙_ SSet.{u} ⟶ X) (d : 𝟙_ SSet.{u} ⟶ Y)
    (n m : ℕ) : ∀ i, 𝟙_ SSet.{u} ⟶ loopCoordinates X Y n m i
  | .inl _ => e
  | .inr _ => d

def pairPowerIso (X Y : SSet.{u}) (n m : ℕ) :
    coordinates (loopCoordinates X Y n m) ≅ finitePower X n ⊗ finitePower Y m where
  hom := { app := fun _ v ↦ ((fun i ↦ v (.inl i)), fun i ↦ v (.inr i)) }
  inv :=
    { app := fun _ v i ↦ match i with | .inl j => v.1 j | .inr j => v.2 j
      naturality := fun _ _ _ ↦ by
        funext v i
        cases i <;> rfl }
  hom_inv_id := by
    apply NatTrans.ext
    funext q v i
    cases i <;> rfl
  inv_hom_id := by ext q v <;> rfl

def groupedCoordinateIso (E X Y F : SSet.{u}) (n m : ℕ) :
    grouped E X Y F n m ≅ padded E (coordinates (loopCoordinates X Y n m)) F :=
  regroupIso E X Y F n m ≪≫
    whiskerLeftIso E (whiskerRightIso (pairPowerIso X Y n m).symm F)

def groupedFace (E : SSet.{u}) {X Y : SSet.{u}}
    (e : 𝟙_ SSet.{u} ⟶ X) (d : 𝟙_ SSet.{u} ⟶ Y) (F : SSet.{u}) (n m : ℕ)
    (S : Set (Fin n ⊕ Fin m)) : (grouped E X Y F n m).Subcomplex :=
  (paddedBoundary E
    (coordinateFace (loopCoordinates X Y n m) (loopUnits e d n m) S) F).preimage
      (groupedCoordinateIso E X Y F n m).hom

/-- Every finite intersection face forgets exactly the constrained coordinates. -/
def groupedFaceIso (E : SSet.{u}) {X Y : SSet.{u}}
    (e : 𝟙_ SSet.{u} ⟶ X) (d : 𝟙_ SSet.{u} ⟶ Y) (F : SSet.{u}) (n m : ℕ)
    (S : Set (Fin n ⊕ Fin m)) :
    (groupedFace E e d F n m S : SSet.{u}) ≅
      padded E (freeCoordinates (loopCoordinates X Y n m) S) F :=
  Arrow.leftFunc.mapIso
    (SSet.Subcomplex.congrArrowι' (groupedCoordinateIso E X Y F n m) rfl) ≪≫
      paddedBoundaryIso E _ F ≪≫
        whiskerLeftIso E (whiskerRightIso (coordinateFaceIso _ _ S) F)

theorem mem_groupedFace (E : SSet.{u}) {X Y : SSet.{u}}
    (e : 𝟙_ SSet.{u} ⟶ X) (d : 𝟙_ SSet.{u} ⟶ Y) (F : SSet.{u}) (n m : ℕ)
    (S : Set (Fin n ⊕ Fin m)) (q : SimplexCategoryᵒᵖ)
    (v : (grouped E X Y F n m).obj q) :
    v ∈ (groupedFace E e d F n m S).obj q ↔
      ∀ i ∈ S, (match i with | .inl j => v.2.1 j | .inr j => v.2.2.1 j) =
        (loopUnits e d n m i).app q PUnit.unit := by
  change (True ∧ _ ∧ True) ↔ _
  simp only [true_and, and_true]
  rfl

theorem groupedFace_union (E : SSet.{u}) {X Y : SSet.{u}}
    (e : 𝟙_ SSet.{u} ⟶ X) (d : 𝟙_ SSet.{u} ⟶ Y) (F : SSet.{u}) (n m : ℕ)
    (S T : Set (Fin n ⊕ Fin m)) :
    groupedFace E e d F n m (S ∪ T) =
      groupedFace E e d F n m S ⊓ groupedFace E e d F n m T := by
  ext q v
  change _ ↔ v ∈ (groupedFace E e d F n m S).obj q ∧
    v ∈ (groupedFace E e d F n m T).obj q
  rw [mem_groupedFace, mem_groupedFace, mem_groupedFace]
  simp only [Set.mem_union]
  aesop

theorem groupedFace_empty (E : SSet.{u}) {X Y : SSet.{u}}
    (e : 𝟙_ SSet.{u} ⟶ X) (d : 𝟙_ SSet.{u} ⟶ Y) (F : SSet.{u}) (n m : ℕ) :
    groupedFace E e d F n m ∅ = ⊤ := by
  ext q v
  simp [mem_groupedFace]

theorem groupedFace_le_boundary (E : SSet.{u}) {X Y : SSet.{u}}
    (e : 𝟙_ SSet.{u} ⟶ X) (d : 𝟙_ SSet.{u} ⟶ Y) (F : SSet.{u}) (n m : ℕ)
    (S : Set (Fin n ⊕ Fin m)) (hS : S.Nonempty) :
    groupedFace E e d F n m S ≤ criticalBoundary E e d F n m := by
  intro q v hv
  obtain ⟨i, hi⟩ := hS
  have h := (mem_groupedFace E e d F n m S q v).1 hv i hi
  apply (mem_criticalBoundary E e d F n m q v).2
  cases i with
  | inl j => exact Or.inl ⟨j, h⟩
  | inr j => exact Or.inr ⟨j, h⟩

@[simp] theorem groupedFaceIso_hom_app (E : SSet.{u}) {X Y : SSet.{u}}
    (e : 𝟙_ SSet.{u} ⟶ X) (d : 𝟙_ SSet.{u} ⟶ Y) (F : SSet.{u}) (n m : ℕ)
    (S : Set (Fin n ⊕ Fin m)) (q : SimplexCategoryᵒᵖ)
    (v : (groupedFace E e d F n m S : SSet.{u}).obj q) :
    (groupedFaceIso E e d F n m S).hom.app q v =
      (v.val.1, ((fun i : {i : Fin n ⊕ Fin m // i ∉ S} ↦
        (pairPowerIso X Y n m).inv.app q
        (v.val.2.1, v.val.2.2.1) i.val), v.val.2.2.2)) := rfl

@[simp] theorem groupedFaceIso_inv_app (E : SSet.{u}) {X Y : SSet.{u}}
    (e : 𝟙_ SSet.{u} ⟶ X) (d : 𝟙_ SSet.{u} ⟶ Y) (F : SSet.{u}) (n m : ℕ)
    (S : Set (Fin n ⊕ Fin m)) (q : SimplexCategoryᵒᵖ)
    (v : (padded E (freeCoordinates (loopCoordinates X Y n m) S) F).obj q) :
    ((groupedFaceIso E e d F n m S).inv.app q v).val =
      (v.1, ((fun j ↦ (insertCoordinates _ (loopUnits e d n m) S).app q v.2.1 (.inl j)),
        ((fun j ↦ (insertCoordinates _ (loopUnits e d n m) S).app q v.2.1 (.inr j)),
          v.2.2))) := rfl

def groupedFaceInsert (E : SSet.{u}) {X Y : SSet.{u}}
    (e : 𝟙_ SSet.{u} ⟶ X) (d : 𝟙_ SSet.{u} ⟶ Y) (F : SSet.{u}) (n m : ℕ)
    (S : Set (Fin n ⊕ Fin m)) :
    padded E (freeCoordinates (loopCoordinates X Y n m) S) F ⟶ grouped E X Y F n m :=
  (groupedFaceIso E e d F n m S).inv ≫ (groupedFace E e d F n m S).ι

@[reassoc (attr := simp)] theorem groupedFaceIso_inclusion (E : SSet.{u})
    {X Y : SSet.{u}} (e : 𝟙_ SSet.{u} ⟶ X) (d : 𝟙_ SSet.{u} ⟶ Y)
    (F : SSet.{u}) (n m : ℕ) (S : Set (Fin n ⊕ Fin m)) :
    (groupedFaceIso E e d F n m S).hom ≫ groupedFaceInsert E e d F n m S =
      (groupedFace E e d F n m S).ι := by
  simp [groupedFaceInsert]

/-- These maps are literally homOfLE on the original constrained tuples. -/
def groupedFaceMap (E : SSet.{u}) {X Y : SSet.{u}}
    (e : 𝟙_ SSet.{u} ⟶ X) (d : 𝟙_ SSet.{u} ⟶ Y) (F : SSet.{u}) (n m : ℕ)
    {S T : Set (Fin n ⊕ Fin m)} (h : T ⊆ S) :
    (groupedFace E e d F n m S : SSet.{u}) ⟶ groupedFace E e d F n m T :=
  SSet.Subcomplex.homOfLE (by
    intro q v hv
    apply (mem_groupedFace E e d F n m T q v).2
    exact fun i hi ↦ (mem_groupedFace E e d F n m S q v).1 hv i (h hi))

@[simp] theorem groupedFaceMap_app (E : SSet.{u}) {X Y : SSet.{u}}
    (e : 𝟙_ SSet.{u} ⟶ X) (d : 𝟙_ SSet.{u} ⟶ Y) (F : SSet.{u}) (n m : ℕ)
    {S T : Set (Fin n ⊕ Fin m)} (h : T ⊆ S) (q : SimplexCategoryᵒᵖ)
    (v : (groupedFace E e d F n m S : SSet.{u}).obj q) :
    ((groupedFaceMap E e d F n m h).app q v).val = v.val := rfl

@[reassoc (attr := simp)] theorem groupedFaceMap_ι (E : SSet.{u}) {X Y : SSet.{u}}
    (e : 𝟙_ SSet.{u} ⟶ X) (d : 𝟙_ SSet.{u} ⟶ Y) (F : SSet.{u}) (n m : ℕ)
    {S T : Set (Fin n ⊕ Fin m)} (h : T ⊆ S) :
    groupedFaceMap E e d F n m h ≫ (groupedFace E e d F n m T).ι =
      (groupedFace E e d F n m S).ι := rfl

def groupedFaceToBoundary (E : SSet.{u}) {X Y : SSet.{u}}
    (e : 𝟙_ SSet.{u} ⟶ X) (d : 𝟙_ SSet.{u} ⟶ Y) (F : SSet.{u}) (n m : ℕ)
    (S : Set (Fin n ⊕ Fin m)) (hS : S.Nonempty) :
    (groupedFace E e d F n m S : SSet.{u}) ⟶ criticalBoundary E e d F n m :=
  SSet.Subcomplex.homOfLE (groupedFace_le_boundary E e d F n m S hS)

theorem criticalBoundary_iSup_faces (E : SSet.{u}) {X Y : SSet.{u}}
    (e : 𝟙_ SSet.{u} ⟶ X) (d : 𝟙_ SSet.{u} ⟶ Y) (F : SSet.{u}) (n m : ℕ) :
    criticalBoundary E e d F n m = ⨆ i, groupedFace E e d F n m {i} := by
  ext q v
  rw [mem_criticalBoundary]
  simp only [SSet.Subcomplex.iSup_obj, Set.mem_iUnion, mem_groupedFace,
    Set.mem_singleton_iff, forall_eq]
  constructor
  · rintro (⟨j, h⟩ | ⟨j, h⟩)
    · exact ⟨.inl j, h⟩
    · exact ⟨.inr j, h⟩
  · rintro ⟨i, h⟩
    cases i with
    | inl j => exact Or.inl ⟨j, h⟩
    | inr j => exact Or.inr ⟨j, h⟩

/-- Finite intersections retain every selected original unit coordinate, not their union. -/
theorem groupedFace_iUnion (E : SSet.{u}) {X Y : SSet.{u}}
    (e : 𝟙_ SSet.{u} ⟶ X) (d : 𝟙_ SSet.{u} ⟶ Y) (F : SSet.{u}) (n m : ℕ)
    {κ : Type} (S : κ → Set (Fin n ⊕ Fin m)) :
    groupedFace E e d F n m (⋃ k, S k) = ⨅ k, groupedFace E e d F n m (S k) := by
  ext q v
  rw [Subfunctor.iInf_obj, Set.mem_iInter]
  change _ ↔ ∀ k, v ∈ (groupedFace E e d F n m (S k)).obj q
  simp only [mem_groupedFace, Set.mem_iUnion]
  constructor
  · intro h k i hi
    exact h i ⟨k, hi⟩
  · rintro h i ⟨k, hi⟩
    exact h k i hi

def groupedFaceUnionSq (E : SSet.{u}) {X Y : SSet.{u}}
    (e : 𝟙_ SSet.{u} ⟶ X) (d : 𝟙_ SSet.{u} ⟶ Y) (F : SSet.{u}) (n m : ℕ)
    (S T : Set (Fin n ⊕ Fin m)) :
    SSet.Subcomplex.Sq
      (groupedFace E e d F n m S ⊓ groupedFace E e d F n m T)
      (groupedFace E e d F n m S) (groupedFace E e d F n m T)
      (groupedFace E e d F n m S ⊔ groupedFace E e d F n m T) where
  inf_eq := rfl
  sup_eq := rfl

/-- Full arbitrary-target pushout UP, using the original homOfLE legs. -/
def groupedFaceUnionIsPushout (E : SSet.{u}) {X Y : SSet.{u}}
    (e : 𝟙_ SSet.{u} ⟶ X) (d : 𝟙_ SSet.{u} ⟶ Y) (F : SSet.{u}) (n m : ℕ)
    (S T : Set (Fin n ⊕ Fin m)) := (groupedFaceUnionSq E e d F n m S T).isPushout

end
end DaggerAmalgamUnitBoundary
