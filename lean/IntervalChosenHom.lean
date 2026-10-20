import IntervalHomIsoContraction
import IntervalFlagDiagonal
import ChosenFlagOriginalHomIso

set_option autoImplicit false

open CategoryTheory EnrichedCategory MonoidalCategory Opposite Simplicial

universe u

namespace DaggerOriginalIntervalChosenHom

noncomputable section

open DaggerChosenRigidificationNecklace hiding E
open DaggerIntervalNecklaceCompletion

abbrev originalHom (z w : (C.{u}.obj E).Obj) : SSet.{u} := z ⟶[SSet.{u}] w

def sourceVertex (z : (C.{u}.obj E).Obj) : E.obj (op ⦋0⦌) := (RV E).symm z

theorem sourceVertex_endpoint (z : (C.{u}.obj E).Obj) : RV E (sourceVertex z) = z :=
  (RV E).apply_symm_apply z

/-- BOTH actual RV endpoint equalities; the original inverse remains explicitly specified. -/
def originalFlagHomIso (z w : (C.{u}.obj E).Obj) :
    flagHom E (sourceVertex z) (sourceVertex w) ≅ originalHom z w :=
  flagOriginalHomIso E (sourceVertex z) (sourceVertex w) ≪≫
    eqToIso (by rw [sourceVertex_endpoint, sourceVertex_endpoint])

theorem originalFlagHomIso_hom (z w : (C.{u}.obj E).Obj) :
    (originalFlagHomIso z w).hom =
      (flagOriginalHomIso E (sourceVertex z) (sourceVertex w)).hom ≫
        targetHomTransport (sourceVertex_endpoint z) (sourceVertex_endpoint w) := rfl

theorem originalFlagHomIso_inv (z w : (C.{u}.obj E).Obj) :
    (originalFlagHomIso z w).inv =
      targetHomTransport (sourceVertex_endpoint z).symm (sourceVertex_endpoint w).symm ≫
        flagOriginalHomInverse E (sourceVertex z) (sourceVertex w) := by
  simp only [originalFlagHomIso, Iso.trans_inv, flagOriginalHomIso_inv]
  rfl

theorem originalFlagHomIso_left (z w : (C.{u}.obj E).Obj) :
    (originalFlagHomIso z w).hom ≫ (originalFlagHomIso z w).inv = 𝟙 _ :=
  (originalFlagHomIso z w).hom_inv_id

theorem originalFlagHomIso_right (z w : (C.{u}.obj E).Obj) :
    (originalFlagHomIso z w).inv ≫ (originalFlagHomIso z w).hom = 𝟙 _ :=
  (originalFlagHomIso z w).inv_hom_id

theorem originalFlagHomIso_operator (z w : (C.{u}.obj E).Obj)
    {q r : SimplexCategoryᵒᵖ} (α : q ⟶ r)
    (p : (flagHom E (sourceVertex z) (sourceVertex w)).obj q) :
    (originalHom z w).map α ((originalFlagHomIso z w).hom.app q p) =
      (originalFlagHomIso z w).hom.app r
        ((flagHom E (sourceVertex z) (sourceVertex w)).map α p) :=
  (congrFun ((originalFlagHomIso z w).hom.naturality α) p).symm

theorem originalFlagHomInverse_operator (z w : (C.{u}.obj E).Obj)
    {q r : SimplexCategoryᵒᵖ} (α : q ⟶ r) (p : (originalHom z w).obj q) :
    (flagHom E (sourceVertex z) (sourceVertex w)).map α
        ((originalFlagHomIso z w).inv.app q p) =
      (originalFlagHomIso z w).inv.app r ((originalHom z w).map α p) :=
  (congrFun ((originalFlagHomIso z w).inv.naturality α) p).symm

def originalIntervalHomContractible (z w : (C.{u}.obj E).Obj) :
    SSet.Contractible (originalHom z w) :=
  contractibleOfIso (originalFlagHomIso z w)
    (DaggerOriginalIntervalFlagContraction.contractible (sourceVertex z) (sourceVertex w))

def originalCenter (z w : (C.{u}.obj E).Obj) : (originalHom z w).obj (op ⦋0⦌) :=
  (originalIntervalHomContractible z w).pt

theorem originalCenter_raw (z w : (C.{u}.obj E).Obj) :
    originalCenter z w =
      (originalFlagHomIso z w).hom.app (op ⦋0⦌)
        (DaggerOriginalIntervalFlagContraction.center
          (a := sourceVertex z) (b := sourceVertex w)) := rfl

theorem originalContraction_map (z w : (C.{u}.obj E).Obj) :
    (originalIntervalHomContractible z w).h.h =
      (originalFlagHomIso z w).inv ▷ (Δ[1] : SSet.{u}) ≫
        (DaggerOriginalIntervalFlagContraction.contraction
          (sourceVertex z) (sourceVertex w)).h ≫ (originalFlagHomIso z w).hom := rfl

theorem originalContraction_app (z w : (C.{u}.obj E).Obj) (q : SimplexCategoryᵒᵖ)
    (x : (originalHom z w).obj q) (t : (Δ[1] : SSet.{u}).obj q) :
    (originalIntervalHomContractible z w).h.h.app q (x, t) =
      (originalFlagHomIso z w).hom.app q
        ((DaggerOriginalIntervalFlagContraction.contraction
          (sourceVertex z) (sourceVertex w)).h.app q
            ((originalFlagHomIso z w).inv.app q x, t)) := rfl

theorem originalContraction_zero (z w : (C.{u}.obj E).Obj) :
    SSet.ι₀ ≫ (originalIntervalHomContractible z w).h.h =
      SSet.const (originalCenter z w) := (originalIntervalHomContractible z w).h.h₀

theorem originalContraction_one (z w : (C.{u}.obj E).Obj) :
    SSet.ι₁ ≫ (originalIntervalHomContractible z w).h.h = 𝟙 (originalHom z w) :=
  (originalIntervalHomContractible z w).h.h₁

theorem originalContraction_operator (z w : (C.{u}.obj E).Obj)
    {q r : SimplexCategoryᵒᵖ} (α : q ⟶ r) (x : (originalHom z w).obj q)
    (t : (Δ[1] : SSet.{u}).obj q) :
    (originalHom z w).map α ((originalIntervalHomContractible z w).h.h.app q (x, t)) =
      (originalIntervalHomContractible z w).h.h.app r
        ((originalHom z w).map α x, (Δ[1] : SSet.{u}).map α t) :=
  (congrFun ((originalIntervalHomContractible z w).h.h.naturality α) (x, t)).symm

end

end DaggerOriginalIntervalChosenHom
