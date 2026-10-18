import ChosenNecklaceGeneralNCMap
import ChosenNecklaceOuterMapTransport
import ChosenNecklaceWedgeFlags

open CategoryTheory EnrichedCategory MonoidalCategory Opposite Simplicial

universe u

namespace DaggerChosenRigidificationNecklace.NecklaceThickening

noncomputable section

open NecklaceCode

variable (T U : NecklaceCode)

def wedgeNCLeft := generalNCMap (wedgeιLeft.{u} T U)
def wedgeNCRight := generalNCMap (wedgeιRight.{u} T U)

theorem wedgeNCLeft_first :
    (wedgeNCLeft.{u} T U).obj (outerLeft T) = outerLeft (wedge T U) := by
  apply congrArg NecklaceThickening.mk
  change mapVertices (wedgeιLeft T U) (ULift.up 0) = _
  rw [wedgeιLeft_vertices, wedgeLeft_first]

theorem wedgeNCRight_last :
    (wedgeNCRight.{u} T U).obj (outerRight U) = outerRight (wedge T U) := by
  apply congrArg NecklaceThickening.mk
  change mapVertices (wedgeιRight T U) (ULift.up (Fin.last U.len)) = _
  rw [wedgeιRight_vertices, wedgeRight_last]

theorem wedgeNC_joint :
    (wedgeNCLeft.{u} T U).obj (outerRight T) =
      (wedgeNCRight.{u} T U).obj (outerLeft U) := by
  apply congrArg NecklaceThickening.mk
  change mapVertices (wedgeιLeft T U) (ULift.up (Fin.last T.len)) =
    mapVertices (wedgeιRight T U) (ULift.up 0)
  rw [wedgeιLeft_vertices, wedgeιRight_vertices, wedge_joint]

/-- The complete original union-of-flags composition, with all three object labels. -/
theorem wedgeFlag_outer_comp (q : SimplexCategoryᵒᵖ)
    (F : NecklaceCode.Flag.{u} T q.unop.len) (G : NecklaceCode.Flag.{u} U q.unop.len) :
    (outerFlagIso (wedge T U)).hom.app q (NecklaceCode.Flag.wedge F G) =
      (targetHomTransport (wedgeNCLeft_first T U) (wedgeNCRight_last T U)).app q
        ((eComp SSet
          ((wedgeNCLeft T U).obj (outerLeft T))
          ((wedgeNCLeft T U).obj (outerRight T))
          ((wedgeNCRight T U).obj (outerRight U))).app q
            (((wedgeNCLeft T U).map (outerLeft T) (outerRight T)).app q
                ((outerFlagIso T).hom.app q F),
              (targetHomTransport (wedgeNC_joint T U).symm rfl).app q
                (((wedgeNCRight T U).map (outerLeft U) (outerRight U)).app q
                  ((outerFlagIso U).hom.app q G)))) := by
  refine CategoryTheory.Functor.ext (fun i ↦ JointPath.ext ?_)
  rw [show targetHomTransport (wedgeNCLeft_first T U) (wedgeNCRight_last T U) =
    castHom (wedgeNCLeft_first T U) (wedgeNCRight_last T U) from rfl, castHom_I]
  change (NecklaceCode.Flag.wedge F G).chain i =
    generalOrderMap (wedgeιLeft T U) '' F.chain i ∪
      (((targetHomTransport (wedgeNC_joint T U).symm rfl).app q
        (((wedgeNCRight T U).map (outerLeft U) (outerRight U)).app q
          ((outerFlagIso U).hom.app q G))).obj i).I
  rw [show targetHomTransport (wedgeNC_joint T U).symm rfl =
    castHom (wedgeNC_joint T U).symm rfl from rfl, castHom_I]
  rfl

end

end DaggerChosenRigidificationNecklace.NecklaceThickening
