import OriginalTaggedReverseFreeCompletion
import DaggerModels.FreeDaggerCofibration
import Mathlib.CategoryTheory.Comma.Arrow
import Mathlib.AlgebraicTopology.SimplicialSet.Boundary
import Mathlib.AlgebraicTopology.SimplicialSet.Horn

/-!
# Actual left-Kan images of the free anti-involutive generators

The comparison is an isomorphism of arrows, retaining both endpoints and
the original map. Free-cofibration membership uses the actual composite
free–forgetful adjunction. No DCH model or weak-equivalence claim is made.
-/

set_option autoImplicit false

open CategoryTheory

universe u

namespace DaggerModels.OriginalTaggedReverseGeneratorComparison

open OriginalTaggedReverseFreeCompletion

noncomputable section

/-- Every original free anti-involutive map has the original free dagger image. -/
def freeMapIso {X Y : SSet.{u}} (i : X ⟶ Y) :
    Arrow.mk (OriginalTaggedReverseAdjunctions.leftKan.map (freeAnti.map i)) ≅
      Arrow.mk (freeDagger.map i) :=
  Arrow.isoOfNatIso freeViaAntiIsoFreeDagger (Arrow.mk i)

/-- The actual free boundary images agree as arrows. -/
def boundaryMapIso (n : ℕ) :
    Arrow.mk (OriginalTaggedReverseAdjunctions.leftKan.map
      (freeAnti.map (SSet.boundary.{u} n).ι)) ≅
        Arrow.mk (freeDagger.map (SSet.boundary.{u} n).ι) :=
  freeMapIso _

/-- The actual free horn images agree as arrows, including every inner horn. -/
def hornMapIso (n : ℕ) (k : Fin (n + 1)) :
    Arrow.mk (OriginalTaggedReverseAdjunctions.leftKan.map
      (freeAnti.map (SSet.horn.{u} n k).ι)) ≅
        Arrow.mk (freeDagger.map (SSet.horn.{u} n k).ι) :=
  freeMapIso _

/-- Actual left-Kan images of free monomorphisms are free cofibrations. -/
theorem freeMap_freeCofibration {X Y : SSet.{u}} (i : X ⟶ Y) [Mono i] :
    DaggerSSet.FreeCofibration
      (OriginalTaggedReverseAdjunctions.leftKan.map (freeAnti.map i)) :=
  freeDagger_map_freeCofibration _ freeViaAntiAdjunction i

/-- In particular the actual free boundary images are free cofibrations. -/
theorem boundaryMap_freeCofibration (n : ℕ) :
    DaggerSSet.FreeCofibration (OriginalTaggedReverseAdjunctions.leftKan.map
      (freeAnti.map (SSet.boundary.{u} n).ι)) :=
  freeMap_freeCofibration _

/-- The actual free horn images are free cofibrations. -/
theorem hornMap_freeCofibration (n : ℕ) (k : Fin (n + 1)) :
    DaggerSSet.FreeCofibration (OriginalTaggedReverseAdjunctions.leftKan.map
      (freeAnti.map (SSet.horn.{u} n k).ι)) :=
  freeMap_freeCofibration _

end

end DaggerModels.OriginalTaggedReverseGeneratorComparison
