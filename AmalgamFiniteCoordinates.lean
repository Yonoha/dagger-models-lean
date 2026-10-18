import OrdinaryWordBoundary
import AmalgamFirstStage
import Mathlib.Data.Fin.Tuple.Basic

/-! Original coordinate products, unit constraints and full constrained-coordinate isos. -/

open CategoryTheory MonoidalCategory CartesianMonoidalCategory Limits

universe u

namespace DaggerAmalgamUnitBoundary

noncomputable section
set_option autoImplicit false

/-- Pointwise products retain every original coordinate and simplex operator. -/
def coordinates {ι : Type} (X : ι → SSet.{u}) : SSet.{u} where
  obj q := ∀ i, (X i).obj q
  map α v i := (X i).map α (v i)
  map_id q := by funext v i; exact FunctorToTypes.map_id_apply _ _
  map_comp α β := by funext v i; exact FunctorToTypes.map_comp_apply _ _ _ _

def coordinate {ι : Type} (X : ι → SSet.{u}) (i : ι) : coordinates X ⟶ X i where
  app _ v := v i

def finitePower (X : SSet.{u}) (n : ℕ) : SSet.{u} := coordinates (fun _ : Fin n ↦ X)

@[simp] theorem finitePower_obj (X : SSet.{u}) (n : ℕ) (q : SimplexCategoryᵒᵖ) :
    (finitePower X n).obj q = (Fin n → X.obj q) := rfl

@[simp] theorem finitePower_map (X : SSet.{u}) (n : ℕ)
    {q q' : SimplexCategoryᵒᵖ} (α : q ⟶ q') (v : Fin n → X.obj q) (i : Fin n) :
    (finitePower X n).map α v i = X.map α (v i) := rfl

def powerEval (X : SSet.{u}) (n : ℕ) (i : Fin n) : finitePower X n ⟶ X :=
  coordinate (fun _ : Fin n ↦ X) i

def powerSuccIso (X : SSet.{u}) (n : ℕ) : finitePower X (n + 1) ≅ X ⊗ finitePower X n where
  hom := { app := fun _ v ↦ (v 0, Fin.tail v) }
  inv :=
    { app := fun _ v ↦ Fin.cons v.1 v.2
      naturality := fun _ _ α ↦ by
        funext v
        exact (Fin.comp_cons (X.map α) v.1 v.2).symm }
  hom_inv_id := by
    apply NatTrans.ext
    funext q v i
    exact congrFun (Fin.cons_self_tail v) i
  inv_hom_id := by ext q v <;> simp [Fin.tail_cons, Fin.cons_zero]

@[simp] theorem powerSuccIso_hom_app (X : SSet.{u}) (n : ℕ)
    (q : SimplexCategoryᵒᵖ) (v : (finitePower X (n + 1)).obj q) :
    (powerSuccIso X n).hom.app q v = (v 0, fun i ↦ v i.succ) := rfl

@[simp] theorem powerSuccIso_inv_app (X : SSet.{u}) (n : ℕ)
    (q : SimplexCategoryᵒᵖ) (v : (X ⊗ finitePower X n).obj q) :
    (powerSuccIso X n).inv.app q v = Fin.cons v.1 v.2 := rfl

def powerZeroIso (X : SSet.{u}) : finitePower X 0 ≅ 𝟙_ SSet.{u} where
  hom := { app := fun _ _ ↦ PUnit.unit }
  inv :=
    { app := fun _ _ ↦ Fin.elim0
      naturality := fun _ _ _ ↦ by funext v i; exact Fin.elim0 i }
  hom_inv_id := by
    apply NatTrans.ext
    funext q v i
    exact Fin.elim0 i
  inv_hom_id := by ext q v; cases v; rfl

@[simp] theorem unit_app_map {X : SSet.{u}} (e : 𝟙_ SSet.{u} ⟶ X)
    {q q' : SimplexCategoryᵒᵖ} (α : q ⟶ q') :
    X.map α (e.app q PUnit.unit) = e.app q' PUnit.unit := by
  exact (congrFun (e.naturality α) PUnit.unit).symm

theorem unitRange_mem {X : SSet.{u}} (e : 𝟙_ SSet.{u} ⟶ X)
    (q : SimplexCategoryᵒᵖ) (v : X.obj q) :
    v ∈ (SSet.Subcomplex.range e).obj q ↔ v = e.app q PUnit.unit := by
  change (∃ z : PUnit, e.app q z = v) ↔ _
  constructor
  · rintro ⟨⟨⟩, h⟩
    exact h.symm
  · intro h
    exact ⟨PUnit.unit, h.symm⟩

def unitRangeArrowIso {X : SSet.{u}} (e : 𝟙_ SSet.{u} ⟶ X) :
    Arrow.mk e ≅ Arrow.mk (SSet.Subcomplex.range e).ι := by
  letI := DaggerAmalgamFirstStage.point_mono e
  exact Arrow.isoMk (asIso (SSet.Subcomplex.toRange e)) (Iso.refl X) (by simp)

/-- ALL selected coordinates are the original unit simplices; others stay arbitrary. -/
def coordinateFace {ι : Type} (X : ι → SSet.{u})
    (e : ∀ i, 𝟙_ SSet.{u} ⟶ X i) (S : Set ι) : (coordinates X).Subcomplex where
  obj q := {v | ∀ i ∈ S, v i = (e i).app q PUnit.unit}
  map α _ hv i hi := by
    change (X i).map α _ = _
    rw [hv i hi, unit_app_map]

def freeCoordinates {ι : Type} (X : ι → SSet.{u}) (S : Set ι) : SSet.{u} :=
  coordinates (fun i : {i // i ∉ S} ↦ X i.val)

def insertCoordinates {ι : Type} (X : ι → SSet.{u})
    (e : ∀ i, 𝟙_ SSet.{u} ⟶ X i) (S : Set ι) : freeCoordinates X S ⟶ coordinates X := by
  classical
  exact
    { app := fun q v i ↦ if hi : i ∈ S then (e i).app q PUnit.unit else v ⟨i, hi⟩
      naturality := fun q q' α ↦ by
        funext v i
        change (if hi : i ∈ S then (e i).app q' PUnit.unit
            else (X i).map α (v ⟨i, hi⟩)) =
          (X i).map α (if hi : i ∈ S then (e i).app q PUnit.unit else v ⟨i, hi⟩)
        by_cases hi : i ∈ S
        · simp only [hi, dif_pos]
          exact (unit_app_map (e i) α).symm
        · simp only [hi]
          rfl }

def faceForget {ι : Type} (X : ι → SSet.{u})
    (e : ∀ i, 𝟙_ SSet.{u} ⟶ X i) (S : Set ι) :
    (coordinateFace X e S : SSet.{u}) ⟶ freeCoordinates X S where
  app _ v i := v.val i.val

def faceInsert {ι : Type} (X : ι → SSet.{u})
    (e : ∀ i, 𝟙_ SSet.{u} ⟶ X i) (S : Set ι) :
    freeCoordinates X S ⟶ (coordinateFace X e S : SSet.{u}) := by
  classical
  exact
    { app := fun q v ↦ ⟨(insertCoordinates X e S).app q v, by
        intro i hi
        simp only [insertCoordinates, hi, dif_pos]⟩
      naturality := fun q q' α ↦ by
        funext v
        apply Subtype.ext
        exact congrFun ((insertCoordinates X e S).naturality α) v }

def coordinateFaceIso {ι : Type} (X : ι → SSet.{u})
    (e : ∀ i, 𝟙_ SSet.{u} ⟶ X i) (S : Set ι) :
    (coordinateFace X e S : SSet.{u}) ≅ freeCoordinates X S := by
  classical
  exact
    { hom := faceForget X e S
      inv := faceInsert X e S
      hom_inv_id := by
        apply NatTrans.ext
        funext q v
        apply Subtype.ext
        change (fun i ↦ if hi : i ∈ S then (e i).app q PUnit.unit
          else v.val i) = v.val
        funext i
        by_cases hi : i ∈ S
        · rw [dif_pos hi]
          exact (v.property i hi).symm
        · rw [dif_neg hi]
      inv_hom_id := by
        apply NatTrans.ext
        funext q v i
        change (if hi : i.val ∈ S then (e i.val).app q PUnit.unit
          else v ⟨i.val, hi⟩) = v i
        rw [dif_neg i.property] }

@[reassoc (attr := simp)] theorem faceInsert_ι {ι : Type} (X : ι → SSet.{u})
    (e : ∀ i, 𝟙_ SSet.{u} ⟶ X i) (S : Set ι) :
    faceInsert X e S ≫ (coordinateFace X e S).ι = insertCoordinates X e S := rfl

theorem coordinateFace_empty {ι : Type} (X : ι → SSet.{u})
    (e : ∀ i, 𝟙_ SSet.{u} ⟶ X i) : coordinateFace X e ∅ = ⊤ := by
  ext q v
  simp [coordinateFace]

theorem coordinateFace_union {ι : Type} (X : ι → SSet.{u})
    (e : ∀ i, 𝟙_ SSet.{u} ⟶ X i) (S T : Set ι) :
    coordinateFace X e (S ∪ T) = coordinateFace X e S ⊓ coordinateFace X e T := by
  ext q v
  change (∀ i ∈ S ∪ T, _) ↔ (∀ i ∈ S, _) ∧ (∀ i ∈ T, _)
  simp only [Set.mem_union]
  aesop

theorem coordinateFace_singleton {ι : Type} (X : ι → SSet.{u})
    (e : ∀ i, 𝟙_ SSet.{u} ⟶ X i) (i : ι) :
    coordinateFace X e {i} = (SSet.Subcomplex.range (e i)).preimage (coordinate X i) := by
  ext q v
  change (∀ j ∈ ({i} : Set ι), v j = (e j).app q PUnit.unit) ↔
    v i ∈ (SSet.Subcomplex.range (e i)).obj q
  rw [unitRange_mem]
  simp

def faceMap {ι : Type} (X : ι → SSet.{u})
    (e : ∀ i, 𝟙_ SSet.{u} ⟶ X i) {S T : Set ι} (h : T ⊆ S) :
    (coordinateFace X e S : SSet.{u}) ⟶ coordinateFace X e T :=
  SSet.Subcomplex.homOfLE (fun _ _ hv i hi ↦ hv i (h hi))

@[simp] theorem faceMap_app {ι : Type} (X : ι → SSet.{u})
    (e : ∀ i, 𝟙_ SSet.{u} ⟶ X i) {S T : Set ι} (h : T ⊆ S)
    (q : SimplexCategoryᵒᵖ) (v : (coordinateFace X e S : SSet.{u}).obj q) :
    ((faceMap X e h).app q v).val = v.val := rfl

@[reassoc (attr := simp)] theorem faceMap_ι {ι : Type} (X : ι → SSet.{u})
    (e : ∀ i, 𝟙_ SSet.{u} ⟶ X i) {S T : Set ι} (h : T ⊆ S) :
    faceMap X e h ≫ (coordinateFace X e T).ι = (coordinateFace X e S).ι := rfl

def faceUnionSq {ι : Type} (X : ι → SSet.{u})
    (e : ∀ i, 𝟙_ SSet.{u} ⟶ X i) (S T : Set ι) :
    SSet.Subcomplex.Sq (coordinateFace X e S ⊓ coordinateFace X e T)
      (coordinateFace X e S) (coordinateFace X e T)
      (coordinateFace X e S ⊔ coordinateFace X e T) where
  inf_eq := rfl
  sup_eq := rfl

def faceUnionIsPushout {ι : Type} (X : ι → SSet.{u})
    (e : ∀ i, 𝟙_ SSet.{u} ⟶ X i) (S T : Set ι) :=
  (faceUnionSq X e S T).isPushout

end
end DaggerAmalgamUnitBoundary
