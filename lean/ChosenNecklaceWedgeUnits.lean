import ChosenNecklaceWedgePushout

open CategoryTheory Limits Opposite Simplicial

universe u

namespace DaggerChosenRigidificationNecklace.NecklaceCode

noncomputable section

variable (T U : NecklaceCode)

theorem pointAt_first_left :
    pointAt T (ULift.up 0) ≫ wedgeιLeft.{u} T U =
      pointAt (wedge T U) (ULift.up 0) := by
  rw [pointAt_comp, wedgeιLeft_vertices, wedgeLeft_first]

theorem pointAt_last_right :
    pointAt U (ULift.up (Fin.last U.len)) ≫ wedgeιRight.{u} T U =
      pointAt (wedge T U) (ULift.up (Fin.last (wedge T U).len)) := by
  rw [pointAt_comp, wedgeιRight_vertices, wedgeRight_last]

theorem wedgeDesc_first {X : SSet.{u}} (f : toSSet.{u} T ⟶ X)
    (g : toSSet.{u} U ⟶ X)
    (h : pointAt T (ULift.up (Fin.last T.len)) ≫ f = pointAt U (ULift.up 0) ≫ g) :
    pointAt (wedge T U) (ULift.up 0) ≫ wedgeDesc T U f g h =
      pointAt T (ULift.up 0) ≫ f := by
  rw [← pointAt_first_left T U, Category.assoc, wedgeDesc_left]

theorem wedgeDesc_last {X : SSet.{u}} (f : toSSet.{u} T ⟶ X)
    (g : toSSet.{u} U ⟶ X)
    (h : pointAt T (ULift.up (Fin.last T.len)) ≫ f = pointAt U (ULift.up 0) ≫ g) :
    pointAt (wedge T U) (ULift.up (Fin.last (wedge T U).len)) ≫
      wedgeDesc T U f g h = pointAt U (ULift.up (Fin.last U.len)) ≫ g := by
  rw [← pointAt_last_right T U, Category.assoc, wedgeDesc_right]

theorem pointAt_point (v : Vertices.{u} point) : pointAt point v = 𝟙 (Δ[0]) := by
  apply NatTrans.ext
  funext q x
  obtain ⟨q⟩ := q
  induction q using SimplexCategory.rec with | _ n
  exact (zeroSimplex_unique _).trans (zeroSimplex_unique x).symm

def wedgeLeftUnit : toSSet.{u} (wedge point T) ≅ toSSet.{u} T where
  hom := wedgeDesc point T (pointAt T (ULift.up 0)) (𝟙 _) (by
    rw [pointAt_point, Category.id_comp, Category.comp_id])
  inv := wedgeιRight point T
  hom_inv_id := by
    apply (wedgeIsPushout point T).hom_ext
    · rw [← Category.assoc, wedgeDesc_left, Category.comp_id]
      rw [← wedge_comm, pointAt_point, Category.id_comp]
    · rw [← Category.assoc, wedgeDesc_right, Category.id_comp, Category.comp_id]
  inv_hom_id := wedgeDesc_right _ _ _ _ _

def wedgeRightUnit : toSSet.{u} (wedge T point) ≅ toSSet.{u} T where
  hom := wedgeDesc T point (𝟙 _) (pointAt T (ULift.up (Fin.last T.len))) (by
    rw [pointAt_point, Category.id_comp, Category.comp_id])
  inv := wedgeιLeft T point
  hom_inv_id := by
    apply (wedgeIsPushout T point).hom_ext
    · rw [← Category.assoc, wedgeDesc_left, Category.id_comp, Category.comp_id]
    · rw [← Category.assoc, wedgeDesc_right, Category.comp_id]
      rw [wedge_comm, pointAt_point, Category.id_comp]
  inv_hom_id := wedgeDesc_left _ _ _ _ _

theorem wedgeLeftUnit_inv : (wedgeLeftUnit.{u} T).inv = wedgeιRight point T := rfl

theorem wedgeRightUnit_inv : (wedgeRightUnit.{u} T).inv = wedgeιLeft T point := rfl

theorem wedgeLeftUnit_point :
    wedgeιLeft.{u} point T ≫ (wedgeLeftUnit T).hom = pointAt T (ULift.up 0) :=
  wedgeDesc_left _ _ _ _ _

theorem wedgeRightUnit_point :
    wedgeιRight.{u} T point ≫ (wedgeRightUnit T).hom =
      pointAt T (ULift.up (Fin.last T.len)) :=
  wedgeDesc_right _ _ _ _ _

end

end DaggerChosenRigidificationNecklace.NecklaceCode
