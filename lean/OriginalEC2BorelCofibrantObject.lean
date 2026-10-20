import OriginalEC2RealizedFreeCellLift
import OriginalEC2RealizationAction

/-!
# Borel cofibrancy of the actual realized EC₂ action

The original codiscrete-nerve action is built from regular C₂-orbit cells.
Each realized cell lifts against equivariant maps whose underlying topological
map is a trivial fibration.  Closure under pushouts and the exhaustive
skeletal colimit gives the lifting property of the actual initial arrow.
-/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra Opposite Simplicial
open DaggerOriginalDaggerRealizationC2Action DaggerOriginalEC2SimplicialAction
open DaggerOriginalEC2SkeletonAction DaggerOriginalEC2EquivariantSkeletalPushout
open DaggerOriginalEC2EquivariantRelativeCellComplex
open DaggerOriginalEC2BorelCofibrancy DaggerOriginalEC2RealizedFreeCellLift
open DaggerOriginalEC2RealizationAction

universe u

namespace DaggerOriginalEC2BorelCofibrantObject

noncomputable section

/-- Each actual realized regular boundary cell has the Borel lifting property. -/
theorem realizedBoundary_borel (n : ℕ) :
    borelCofibrations.{u}
      ((SSet.toTop.{u}.mapAction C2.{u}).map (boundaryHom.{u} n)) := by
  intro X Y p hp
  exact realized_freeCellMap_lifts (SSet.boundary.{u} n).ι p
    (hp _ (MorphismProperty.ofHoms.mk n))

/-- The actual original skeletal inclusion has the Borel lifting property. -/
theorem realizedSkeletalInclusion_borel :
    borelCofibrations.{u}
      ((SSet.toTop.{u}.mapAction C2.{u}).map (skeletonInclusion.{u} 0)) :=
  realizedSkeletalInclusion_borel_of_cells realizedBoundary_borel

/-- The realized zero skeleton of the original action is initial. -/
def realizedSkeletalZeroIsInitial :
    IsInitial ((SSet.toTop.{u}.mapAction C2.{u}).obj (skeletonAction.{u} 0)) :=
  (skeletalZeroIsInitial.{u}).isInitialObj (SSet.toTop.{u}.mapAction C2.{u})

/-- The actual realized EC₂ action is Borel cofibrant: its initial arrow lifts
against every equivariant map with underlying topological trivial fibration. -/
theorem actualRealizedEC2_borelCofibrant :
    borelCofibrations.{u}
      ((realizedSkeletalZeroIsInitial.{u}).to realizedEC2Action.{u}) := by
  have h : (realizedSkeletalZeroIsInitial.{u}).to realizedEC2Action.{u} =
      (SSet.toTop.{u}.mapAction C2.{u}).map (skeletonInclusion.{u} 0) :=
    (realizedSkeletalZeroIsInitial.{u}).hom_ext _ _
  rw [h]
  exact realizedSkeletalInclusion_borel.{u}

end

end DaggerOriginalEC2BorelCofibrantObject
