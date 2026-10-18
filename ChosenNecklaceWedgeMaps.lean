import ChosenNecklaceOrderLift
import ChosenNecklaceWedgeCode
import ChosenNecklaceCategory

open CategoryTheory Limits Opposite Simplicial

universe u

namespace DaggerChosenRigidificationNecklace.NecklaceCode

noncomputable section

def pointAt (T : NecklaceCode) (v : Vertices.{u} T) : Δ[0] ⟶ toSSet.{u} T :=
  SSet.yonedaEquiv.symm (T.verticesEquiv.symm v)

theorem pointAt_vertex (T : NecklaceCode) (v : Vertices.{u} T) :
    SSet.yonedaEquiv (pointAt T v) = T.verticesEquiv.symm v :=
  SSet.yonedaEquiv.apply_symm_apply _

theorem pointAt_comp {T U : NecklaceCode} (v : Vertices.{u} T)
    (f : toSSet.{u} T ⟶ toSSet.{u} U) :
    pointAt T v ≫ f = pointAt U (mapVertices f v) := by
  apply SSet.yonedaEquiv.injective
  rw [SSet.yonedaEquiv_comp, pointAt_vertex, pointAt_vertex]
  exact (U.verticesEquiv.symm_apply_apply _).symm

variable (T U : NecklaceCode)

theorem wedgeLeft_image :
    BeadImageCondition (T := T) (U := wedge T U) (wedgeLeft T U).toOrderHom := by
  intro b
  left
  exact ⟨wedgeLeftBead T U b, wedgeLeftBead_interval T U b⟩

theorem wedgeRight_image :
    BeadImageCondition (T := U) (U := wedge T U) (wedgeRight T U).toOrderHom := by
  intro b
  left
  exact ⟨wedgeRightBead T U b, wedgeRightBead_interval T U b⟩

def wedgeιLeft : toSSet.{u} T ⟶ toSSet.{u} (wedge T U) :=
  orderLift (wedgeLeft T U).toOrderHom (wedgeLeft_image T U)

def wedgeιRight : toSSet.{u} U ⟶ toSSet.{u} (wedge T U) :=
  orderLift (wedgeRight T U).toOrderHom (wedgeRight_image T U)

theorem wedgeιLeft_vertices (v : Vertices.{u} T) :
    mapVertices (wedgeιLeft T U) v = ULift.up (wedgeLeft T U v.down) :=
  orderLift_vertices _ _ v

theorem wedgeιRight_vertices (v : Vertices.{u} U) :
    mapVertices (wedgeιRight T U) v = ULift.up (wedgeRight T U v.down) :=
  orderLift_vertices _ _ v

theorem wedgeιLeft_inclusion :
    wedgeιLeft.{u} T U ≫ (wedge T U).inclusion =
      T.inclusion ≫ SSet.stdSimplex.map
        (SimplexCategory.Hom.mk (wedgeLeft T U).toOrderHom : ⦋T.len⦌ ⟶ ⦋(wedge T U).len⦌) :=
  orderLift_inclusion _ _

theorem wedgeιRight_inclusion :
    wedgeιRight.{u} T U ≫ (wedge T U).inclusion =
      U.inclusion ≫ SSet.stdSimplex.map
        (SimplexCategory.Hom.mk (wedgeRight T U).toOrderHom : ⦋U.len⦌ ⟶ ⦋(wedge T U).len⦌) :=
  orderLift_inclusion _ _

theorem wedge_comm :
    pointAt T (ULift.up (Fin.last T.len)) ≫ wedgeιLeft.{u} T U =
      pointAt U (ULift.up 0) ≫ wedgeιRight T U := by
  rw [pointAt_comp, pointAt_comp, wedgeιLeft_vertices, wedgeιRight_vertices, wedge_joint]

theorem wedgeιLeft_first :
    (wedgeιLeft.{u} T U).app _ T.first = (wedge T U).first := by
  apply (wedge T U).verticesEquiv.injective
  have h := wedgeιLeft_vertices T U (ULift.up 0 : Vertices.{u} T)
  simpa only [mapVertices, first, wedgeLeft_first, Equiv.apply_symm_apply] using h

theorem wedgeιRight_last :
    (wedgeιRight.{u} T U).app _ U.last = (wedge T U).last := by
  apply (wedge T U).verticesEquiv.injective
  have h := wedgeιRight_vertices T U (ULift.up (Fin.last U.len) : Vertices.{u} U)
  simpa only [mapVertices, last, wedgeRight_last, Equiv.apply_symm_apply] using h

end

end DaggerChosenRigidificationNecklace.NecklaceCode
