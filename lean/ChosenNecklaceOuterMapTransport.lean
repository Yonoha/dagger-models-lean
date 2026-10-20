import ChosenNecklaceEnrichedFunctor
import ChosenEnrichedMapTransport

open CategoryTheory EnrichedCategory MonoidalCategory Opposite Simplicial

universe u

namespace DaggerChosenRigidificationNecklace.NecklaceThickening

noncomputable section

open NecklaceCode

def outerLeft (T : NecklaceCode) : (NC.{u} T).Obj := ⟨ULift.up 0⟩
def outerRight (T : NecklaceCode) : (NC.{u} T).Obj := ⟨ULift.up (Fin.last T.len)⟩

theorem NCMap_outerLeft {T U : NecklaceCode} (h : NecklaceCode.Hom.{u} T U) :
    (NCMap h).obj (outerLeft T) = outerLeft U :=
  congrArg NecklaceThickening.mk (ULift.ext _ _ (orderMap_first h))

theorem NCMap_outerRight {T U : NecklaceCode} (h : NecklaceCode.Hom.{u} T U) :
    (NCMap h).obj (outerRight T) = outerRight U :=
  congrArg NecklaceThickening.mk (ULift.ext _ _ (orderMap_last h))

/-- The original outer path direct image is the full NC Hom map with both endpoint casts. -/
theorem outerMap_original {T U : NecklaceCode} (h : NecklaceCode.Hom.{u} T U) :
    nerveMap (mapOuterPathFunctor h) =
      (NCMap h).map (outerLeft T) (outerRight T) ≫
        targetHomTransport (NCMap_outerLeft h) (NCMap_outerRight h) := by
  ext q F
  refine CategoryTheory.Functor.ext (fun i ↦ JointPath.ext ?_)
  change (mapOuterPathFunctor h |>.obj (F.obj i)).I =
    (((targetHomTransport (NCMap_outerLeft h) (NCMap_outerRight h)).app q
      (((NCMap h).map (outerLeft T) (outerRight T)).app q F)).obj i).I
  rw [show targetHomTransport (NCMap_outerLeft h) (NCMap_outerRight h) =
    castHom (NCMap_outerLeft h) (NCMap_outerRight h) from rfl, castHom_I]
  rfl

end

end DaggerChosenRigidificationNecklace.NecklaceThickening
