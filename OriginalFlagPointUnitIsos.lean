import OriginalFlagZeroBeadPoint
import ChosenNecklacesOverWedge

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial

universe u

namespace DaggerOriginalFlagFlankification

noncomputable section

open DaggerChosenRigidificationNecklace NecklaceCode

variable {X : SSet.{u}} {a b : X.obj (op ⦋0⦌)}

/-- The inverse is the EXISTING right inclusion; only its endpoint record is supplied. -/
def pointLeftUnitCodeInv (T : NecklaceCode) :
    NecklaceCode.Hom.{u} T (NecklaceCode.wedge NecklaceCode.point T) where
  map := (wedgeLeftUnit T).inv
  first := first_of_point _ (by
    change pointAt T (ULift.up 0) ≫ wedgeιRight NecklaceCode.point T = _
    rw [← pointAt_first_left NecklaceCode.point T, ← wedge_comm,
      pointAt_point, pointAt_point])
  last := wedgeιRight_last NecklaceCode.point T

/-- The inverse is the EXISTING left inclusion, with the same terminal vertex. -/
def pointRightUnitCodeInv (T : NecklaceCode) :
    NecklaceCode.Hom.{u} T (NecklaceCode.wedge T NecklaceCode.point) where
  map := (wedgeRightUnit T).inv
  first := wedgeιLeft_first T NecklaceCode.point
  last := last_of_point _ (by
    change pointAt T (ULift.up (Fin.last T.len)) ≫ wedgeιLeft T NecklaceCode.point = _
    rw [← pointAt_last_right T NecklaceCode.point, wedge_comm,
      pointAt_point, pointAt_point])

def pointLeftUnitInv (P : NecklacesOver X a b) :
    P ⟶ NecklacesOver.wedge (NecklacesOver.point a) P where
  hom := pointLeftUnitCodeInv P.code
  w := NecklacesOver.wedge_right (NecklacesOver.point a) P

def pointRightUnitInv (P : NecklacesOver X a b) :
    P ⟶ NecklacesOver.wedge P (NecklacesOver.point b) where
  hom := pointRightUnitCodeInv P.code
  w := NecklacesOver.wedge_left P (NecklacesOver.point b)

/-- Reuse of the actual forward unit and raw SSet inverse laws, now wholly over X. -/
def pointLeftUnitIso (P : NecklacesOver X a b) :
    NecklacesOver.wedge (NecklacesOver.point a) P ≅ P where
  hom := NecklacesOver.wedgeLeftUnitOver P
  inv := pointLeftUnitInv P
  hom_inv_id := by
    apply NecklacesOver.Hom.ext
    apply NecklaceCode.Hom.ext
    exact (wedgeLeftUnit P.code).hom_inv_id
  inv_hom_id := by
    apply NecklacesOver.Hom.ext
    apply NecklaceCode.Hom.ext
    exact (wedgeLeftUnit P.code).inv_hom_id

def pointRightUnitIso (P : NecklacesOver X a b) :
    NecklacesOver.wedge P (NecklacesOver.point b) ≅ P where
  hom := NecklacesOver.wedgeRightUnitOver P
  inv := pointRightUnitInv P
  hom_inv_id := by
    apply NecklacesOver.Hom.ext
    apply NecklaceCode.Hom.ext
    exact (wedgeRightUnit P.code).hom_inv_id
  inv_hom_id := by
    apply NecklacesOver.Hom.ext
    apply NecklaceCode.Hom.ext
    exact (wedgeRightUnit P.code).inv_hom_id

theorem pointLeftUnitIso_hom (P : NecklacesOver X a b) :
    (pointLeftUnitIso P).hom.hom.map = (wedgeLeftUnit P.code).hom := rfl

theorem pointLeftUnitIso_inv (P : NecklacesOver X a b) :
    (pointLeftUnitIso P).inv.hom.map = wedgeιRight NecklaceCode.point P.code := rfl

theorem pointRightUnitIso_hom (P : NecklacesOver X a b) :
    (pointRightUnitIso P).hom.hom.map = (wedgeRightUnit P.code).hom := rfl

theorem pointRightUnitIso_inv (P : NecklacesOver X a b) :
    (pointRightUnitIso P).inv.hom.map = wedgeιLeft P.code NecklaceCode.point := rfl

theorem pointLeftUnitIso_hom_triangle (P : NecklacesOver X a b) :
    (pointLeftUnitIso P).hom.hom.map ≫ P.map =
      (NecklacesOver.wedge (NecklacesOver.point a) P).map :=
  (pointLeftUnitIso P).hom.w

theorem pointLeftUnitIso_inv_triangle (P : NecklacesOver X a b) :
    (pointLeftUnitIso P).inv.hom.map ≫
        (NecklacesOver.wedge (NecklacesOver.point a) P).map = P.map :=
  (pointLeftUnitIso P).inv.w

theorem pointRightUnitIso_hom_triangle (P : NecklacesOver X a b) :
    (pointRightUnitIso P).hom.hom.map ≫ P.map =
      (NecklacesOver.wedge P (NecklacesOver.point b)).map :=
  (pointRightUnitIso P).hom.w

theorem pointRightUnitIso_inv_triangle (P : NecklacesOver X a b) :
    (pointRightUnitIso P).inv.hom.map ≫
        (NecklacesOver.wedge P (NecklacesOver.point b)).map = P.map :=
  (pointRightUnitIso P).inv.w

end

end DaggerOriginalFlagFlankification
