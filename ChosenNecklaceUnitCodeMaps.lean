import ChosenNecklaceWedgeFunctor

open CategoryTheory Limits Opposite Simplicial

universe u

namespace DaggerChosenRigidificationNecklace.NecklaceCode

noncomputable section

variable (T : NecklaceCode)

def wedgeLeftUnitCode : Hom.{u} (wedge point T) T where
  map := (wedgeLeftUnit T).hom
  first := first_of_point _ (by
    dsimp only [wedgeLeftUnit, wedgeRightUnit]
    rw [wedgeDesc_first, pointAt_point, Category.id_comp])
  last := last_of_point _ (by
    dsimp only [wedgeLeftUnit, wedgeRightUnit]
    rw [wedgeDesc_last, Category.comp_id])

def wedgeRightUnitCode : Hom.{u} (wedge T point) T where
  map := (wedgeRightUnit T).hom
  first := first_of_point _ (by
    dsimp only [wedgeLeftUnit, wedgeRightUnit]
    rw [wedgeDesc_first, Category.comp_id])
  last := last_of_point _ (by
    dsimp only [wedgeLeftUnit, wedgeRightUnit]
    rw [wedgeDesc_last, pointAt_point, Category.id_comp])

theorem pointAt_vertex_apply {X : SSet.{u}} (x : X.obj (op ⦋0⦌))
    (v : (Δ[0] : SSet.{u}).obj (op ⦋0⦌)) : (SSet.yonedaEquiv.symm x).app _ v = x := by
  have hv : v = SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{u})) :=
    (zeroSimplex_unique v).trans (zeroSimplex_unique _).symm
  rw [hv, ← SSet.yonedaEquiv_comp, Category.id_comp, SSet.yonedaEquiv.apply_symm_apply]

end

end DaggerChosenRigidificationNecklace.NecklaceCode
