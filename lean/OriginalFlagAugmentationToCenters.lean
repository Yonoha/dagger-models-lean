import OriginalFlagAugmentationCenters

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial

universe u

namespace DaggerOriginalFlagFlankification

noncomputable section

open DaggerChosenRigidificationNecklace NecklaceCode

variable (X : SSet.{u}) (a b : X.obj (op ⦋0⦌)) (n : ℕ)

def degreeInOwnFiber (p : Degree X a b n) : Fiber X a b n (classOf X a b n p) :=
  ⟨p, rfl⟩

def flankInOwnFiber (p : Degree X a b n) :
    FlankedFiber X a b n (classOf X a b n p) :=
  (flankToFlankedFiber X a b n (classOf X a b n p)).obj (degreeInOwnFiber X a b n p)

/-- Forget only the two fiber proofs of the exact terminal arrow. -/
def flankToCenterArrow (p : Degree X a b n) :
    (flankification X a b n).obj p ⟶ centerDegreeObj X a b n (classOf X a b n p) :=
  ((fiberCenterIsTerminal X a b n (classOf X a b n p)).from
    (flankInOwnFiber X a b n p)).hom.hom

theorem flankToCenterArrow_whole (p : Degree X a b n) :
    (flankToCenterArrow X a b n p).val.hom.map =
      (((fiberCenterIsTerminal X a b n (classOf X a b n p)).from
        (flankInOwnFiber X a b n p)).hom.hom).val.hom.map := rfl

/-- Both composites are compared in the actual FlankedDegree, not after mapping into X. -/
theorem flankToCenterArrow_naturality {p q : Degree X a b n} (f : p ⟶ q) :
    (flankification X a b n).map f ≫ flankToCenterArrow X a b n q =
      flankToCenterArrow X a b n p ≫
        (augmentation X a b n ⋙ centers X a b n).map f := by
  let pF : FlankedDegree X a b n := (toFlankedDegree X a b n).obj p
  let qC : FlankedDegree X a b n := centerFlankedDegreeObj X a b n (classOf X a b n q)
  have h := flankedDegree_hom_unique pF qC
    (centerDegreeObj_nondegenerate X a b n (classOf X a b n q))
    (ObjectProperty.homMk
      ((flankification X a b n).map f ≫ flankToCenterArrow X a b n q))
    (ObjectProperty.homMk
      (flankToCenterArrow X a b n p ≫
        (augmentation X a b n ⋙ centers X a b n).map f))
  exact congrArg (fun k : pF ⟶ qC ↦ k.hom) h

def toCenters :
    flankification X a b n ⟶ augmentation X a b n ⋙ centers X a b n where
  app := flankToCenterArrow X a b n
  naturality _ _ f := flankToCenterArrow_naturality X a b n f

theorem toCenters_app (p : Degree X a b n) :
    (toCenters X a b n).app p = flankToCenterArrow X a b n p := rfl

/-- The whole over-X triangle retains the original map of the original flank object. -/
theorem toCenters_triangle (p : Degree X a b n) :
    ((toCenters X a b n).app p).val.hom.map ≫
        (centerDegreeObj X a b n (classOf X a b n p)).1.map =
      ((flankification X a b n).obj p).1.map :=
  ((toCenters X a b n).app p).val.w

theorem toCenters_first (p : Degree X a b n) :
    ((toCenters X a b n).app p).val.hom.map.app (op ⦋0⦌)
        ((flankification X a b n).obj p).1.code.first =
      (centerDegreeObj X a b n (classOf X a b n p)).1.code.first :=
  ((toCenters X a b n).app p).val.hom.first

theorem toCenters_last (p : Degree X a b n) :
    ((toCenters X a b n).app p).val.hom.map.app (op ⦋0⦌)
        ((flankification X a b n).obj p).1.code.last =
      (centerDegreeObj X a b n (classOf X a b n p)).1.code.last :=
  ((toCenters X a b n).app p).val.hom.last

theorem toCenters_flag (p : Degree X a b n) :
    NecklaceCode.Flag.map ((toCenters X a b n).app p).val.hom
        ((flankification X a b n).obj p).2 =
      (centerDegreeObj X a b n (classOf X a b n p)).2 :=
  ((toCenters X a b n).app p).property

end

end DaggerOriginalFlagFlankification
