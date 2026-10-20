import AmalgamUnitBoundary

/-! Full original rank-zero products and the exceptional NN1 inclusion. -/

open CategoryTheory MonoidalCategory CartesianMonoidalCategory DaggerModels
open DaggerAmalgamUnitBoundary

universe u
namespace DaggerAmalgamLowRankProducts
noncomputable section
set_option autoImplicit false

/-- Remove only the literal empty coordinate function. -/
def zeroTailIso (X F : SSet.{u}) : finitePower X 0 ⊗ F ≅ F :=
  whiskerRightIso (powerZeroIso X) F ≪≫ λ_ F

@[simp] theorem zeroTailIso_hom_app (X F : SSet.{u}) (q : SimplexCategoryᵒᵖ)
    (v : (finitePower X 0 ⊗ F).obj q) :
    (zeroTailIso X F).hom.app q v = v.2 := rfl

@[simp] theorem zeroTailIso_inv_app (X F : SSet.{u}) (q : SimplexCategoryᵒᵖ)
    (v : F.obj q) : (zeroTailIso X F).inv.app q v = (Fin.elim0, v) := rfl

/-- Both original Fin0 fields remain in the inverse. -/
def groupedZeroIso (E X Y F : SSet.{u}) : grouped E X Y F 0 0 ≅ E ⊗ F :=
  whiskerLeftIso E (whiskerLeftIso (finitePower X 0) (zeroTailIso Y F) ≪≫
    zeroTailIso X F)

@[simp] theorem groupedZeroIso_hom_app (E X Y F : SSet.{u}) (q : SimplexCategoryᵒᵖ)
    (v : (grouped E X Y F 0 0).obj q) :
    (groupedZeroIso E X Y F).hom.app q v = (v.1, v.2.2.2) := rfl

@[simp] theorem groupedZeroIso_inv_app (E X Y F : SSet.{u}) (q : SimplexCategoryᵒᵖ)
    (v : (E ⊗ F).obj q) :
    (groupedZeroIso E X Y F).inv.app q v = (v.1, Fin.elim0, Fin.elim0, v.2) := rfl

/-- The full one-coordinate object is the original simplicial set. -/
def powerOneIso (X : SSet.{u}) : finitePower X 1 ≅ X :=
  powerSuccIso X 0 ≪≫ whiskerLeftIso X (powerZeroIso X) ≪≫ ρ_ X

@[simp] theorem powerOneIso_hom_app (X : SSet.{u}) (q : SimplexCategoryᵒᵖ)
    (v : (finitePower X 1).obj q) : (powerOneIso X).hom.app q v = v 0 := rfl

@[simp] theorem powerOneIso_inv_app (X : SSet.{u}) (q : SimplexCategoryᵒᵖ)
    (v : X.obj q) : (powerOneIso X).inv.app q v = Fin.cons v Fin.elim0 := rfl

variable (C B : SimplicialCat.{u, u}) (x : C.Obj) (b : B.Obj)

def zeroOOIso (a d : C.Obj) : familyOO C B x b a d 0 ≅ (a ⟶[SSet] d) := Iso.refl _

def zeroONIso (a : C.Obj) (w : B.Obj) :
    familyON C B x b a w 0 ≅ (a ⟶[SSet] x) ⊗ (b ⟶[SSet] w) :=
  groupedZeroIso _ _ _ _

def zeroNOIso (z : B.Obj) (d : C.Obj) :
    familyNO C B x b z d 0 ≅ (z ⟶[SSet] b) ⊗ (x ⟶[SSet] d) :=
  groupedZeroIso _ _ _ _

def zeroNNIso (z w : B.Obj) : familyNN C B x b z w 0 ≅ (z ⟶[SSet] w) := Iso.refl _

/-- The actual original associator gives the first-stage target, with empty B coordinates. -/
def oneNNIso (z w : B.Obj) : familyNN C B x b z w 1 ≅
    ((z ⟶[SSet] b) ⊗ (x ⟶[SSet] x)) ⊗ (b ⟶[SSet] w) :=
  whiskerLeftIso _ (whiskerLeftIso _ (zeroTailIso _ _) ≪≫
    whiskerRightIso (powerOneIso _) _) ≪≫ (α_ _ _ _).symm

@[simp] theorem oneNNIso_hom_app (z w : B.Obj) (q : SimplexCategoryᵒᵖ)
    (v : (familyNN C B x b z w 1).obj q) :
    (oneNNIso C B x b z w).hom.app q v = ((v.1, v.2.1 0), v.2.2.2) := rfl

@[simp] theorem oneNNIso_inv_app (z w : B.Obj) (q : SimplexCategoryᵒᵖ)
    (v : (((z ⟶[SSet] b) ⊗ (x ⟶[SSet] x)) ⊗ (b ⟶[SSet] w)).obj q) :
    (oneNNIso C B x b z w).inv.app q v =
      (v.1.1, Fin.cons v.1.2 Fin.elim0, Fin.elim0, v.2) := rfl

/-- Forget only the constrained C-loop unit; retain both endpoint arrows. -/
def oneNNBoundaryIso (z w : B.Obj) : (boundaryNN C B x b z w 1 : SSet.{u}) ≅
    (z ⟶[SSet] b) ⊗ (b ⟶[SSet] w) where
  hom := { app := fun _ v ↦ (v.val.1, v.val.2.2.2) }
  inv :=
    { app := fun q v ↦ ⟨(v.1, Fin.cons ((eId SSet x).app q PUnit.unit) Fin.elim0,
        Fin.elim0, v.2), (mem_boundaryNN_one C B x b z w q _).2 rfl⟩
      naturality := fun q q' α ↦ by
        funext v
        apply Subtype.ext
        apply Prod.ext
        · rfl
        · apply Prod.ext
          · change Fin.cons ((eId SSet x).app q' PUnit.unit)
                (Fin.elim0 : Fin 0 → (x ⟶[SSet] x).obj q') =
              (x ⟶[SSet] x).map α ∘
                Fin.cons ((eId SSet x).app q PUnit.unit) Fin.elim0
            rw [← unit_app_map (eId SSet x) α]
            have ht : (x ⟶[SSet] x).map α ∘
                (Fin.elim0 : Fin 0 → (x ⟶[SSet] x).obj q) = Fin.elim0 := by
              funext i
              exact Fin.elim0 i
            simpa only [ht] using (Fin.comp_cons ((x ⟶[SSet] x).map α)
              ((eId SSet x).app q PUnit.unit) (Fin.elim0 : Fin 0 → _)).symm
          · apply Prod.ext
            · funext i
              exact Fin.elim0 i
            · rfl }
  hom_inv_id := by
    apply NatTrans.ext
    funext q v
    apply Subtype.ext
    change (v.val.1, Fin.cons ((eId SSet x).app q PUnit.unit) Fin.elim0,
      Fin.elim0, v.val.2.2.2) = v.val
    have hv := (mem_boundaryNN_one C B x b z w q v.val).1 v.property
    have hx : Fin.cons ((eId SSet x).app q PUnit.unit) Fin.elim0 = v.val.2.1 := by
      rw [← hv]
      have ht : Fin.elim0 = Fin.tail v.val.2.1 := by funext i; exact Fin.elim0 i
      rw [ht]
      exact Fin.cons_self_tail _
    have hy : Fin.elim0 = v.val.2.2.1 := by funext i; exact Fin.elim0 i
    rw [hx, hy]
    simp only [Prod.eta]
  inv_hom_id := by ext q v <;> rfl

@[simp] theorem oneNNBoundaryIso_hom_app (z w : B.Obj) (q : SimplexCategoryᵒᵖ)
    (v : (boundaryNN C B x b z w 1 : SSet.{u}).obj q) :
    (oneNNBoundaryIso C B x b z w).hom.app q v = (v.val.1, v.val.2.2.2) := rfl

@[simp] theorem oneNNBoundaryIso_inv_val (z w : B.Obj) (q : SimplexCategoryᵒᵖ)
    (v : ((z ⟶[SSet] b) ⊗ (b ⟶[SSet] w)).obj q) :
    ((oneNNBoundaryIso C B x b z w).inv.app q v).val =
      (v.1, Fin.cons ((eId SSet x).app q PUnit.unit) Fin.elim0, Fin.elim0, v.2) := rfl

/-- SAME boundary inclusion, SAME first-stage unit arrow and actual associator. -/
theorem oneNNBoundaryIso_square (z w : B.Obj) :
    (oneNNBoundaryIso C B x b z w).hom ≫
        (DaggerAmalgamFirstStage.atRight (z ⟶[SSet] b) (eId SSet x) ▷ (b ⟶[SSet] w)) =
      (boundaryNN C B x b z w 1).ι ≫ (oneNNIso C B x b z w).hom := by
  apply NatTrans.ext
  funext q v
  change ((v.val.1, (eId SSet x).app q PUnit.unit), v.val.2.2.2) =
    ((v.val.1, v.val.2.1 0), v.val.2.2.2)
  rw [(mem_boundaryNN_one C B x b z w q v.val).1 v.property]

def oneNNBoundaryArrowIso (z w : B.Obj) :
    Arrow.mk (boundaryNN C B x b z w 1).ι ≅
      Arrow.mk (DaggerAmalgamFirstStage.atRight (z ⟶[SSet] b) (eId SSet x) ▷
        (b ⟶[SSet] w)) :=
  Arrow.isoMk (oneNNBoundaryIso C B x b z w) (oneNNIso C B x b z w)
    (oneNNBoundaryIso_square C B x b z w)

end
end DaggerAmalgamLowRankProducts
