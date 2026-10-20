import DaggerModels.Presentable
import DaggerModels.FreeBoundary
import DaggerModels.RelativeCellPresentation
import DaggerModels.SmallObjectFiniteDomains
import TopCatModelCategory.SSet.Presentable
import Mathlib.CategoryTheory.Presentable.Adjunction
import Mathlib.CategoryTheory.SmallObject.Basic

/-! The literal free boundaries generate the entire original free-cofibration left class. -/

set_option autoImplicit false
open CategoryTheory DaggerModels MorphismProperty
universe u

namespace DaggerOriginalFreeCofibrationGeneration

noncomputable section
attribute [local instance] Cardinal.fact_isRegular_aleph0
attribute [local instance] SmallObjectFiniteDomains.aleph0OrdOrderBot
attribute [local instance] daggerSSetHasColimits DaggerSSet.forget_preservesColimits

/-- The original forgetful functor preserves filtered colimits by its existing colimit theorem. -/
instance forgetAccessible : DaggerSSet.forget.{u}.IsCardinalAccessible Cardinal.aleph0.{u} where

/-- Each original free boundary domain is finitely presentable through the actual adjunction. -/
theorem freeBoundary_domain_isFinitelyPresentable (n : ℕ) :
    IsFinitelyPresentable.{u} (freeDagger.obj (SSet.boundary.{u} n).toSSet) :=
  freeDaggerAdjunction.isCardinalPresentable_leftAdjoint_obj Cardinal.aleph0 _

/-- The literal countable family is small in the original category and universe. -/
instance boundaryFamily_isSmall : IsSmall.{u} (freeBoundaryGenerators freeDagger.{u}) := by
  change IsSmall.{u} (ofHoms (fun n : ℕ ↦ freeDagger.map (SSet.boundary.{u} n).ι))
  exact isSmall_ofHoms _

/-- Every arrow in the actual generator predicate has its original finitely presentable domain. -/
theorem boundaryFamily_domain_isFinitelyPresentable {A B : DaggerSSet.{u}} (i : A ⟶ B)
    (hi : freeBoundaryGenerators freeDagger i) : IsFinitelyPresentable.{u} A := by
  change ofHoms (fun n : ℕ ↦ freeDagger.map (SSet.boundary.{u} n).ι) i at hi
  obtain ⟨n, h⟩ := (ofHoms_iff _ i).mp hi
  have hA : A = freeDagger.obj (SSet.boundary.{u} n).toSSet :=
    congrArg (fun a : Arrow DaggerSSet.{u} ↦ a.left) h
  rw [hA]
  exact freeBoundary_domain_isFinitelyPresentable n

/-- Native smallness holds at aleph0 for the original family, without supplied Smith data. -/
instance boundaryCardinal :
    (freeBoundaryGenerators freeDagger.{u}).IsCardinalForSmallObjectArgument
      Cardinal.aleph0.{u} :=
  SmallObjectFiniteDomains.isCardinalForSmallObjectArgument_aleph0.{u} _
    (fun i hi ↦ boundaryFamily_domain_isFinitelyPresentable i hi)

/-- The actual original free boundaries admit the native small object argument. -/
instance boundarySmallObjectArgument :
    HasSmallObjectArgument.{u} (freeBoundaryGenerators freeDagger.{u}) :=
  SmallObjectFiniteDomains.hasSmallObjectArgument.{u} _
    (fun i hi ↦ boundaryFamily_domain_isFinitelyPresentable i hi)

/-- The whole original free-cofibration class is precisely the generated left lifting class. -/
theorem boundary_rlp_llp_eq_freeCof : (freeBoundaryGenerators freeDagger.{u}).rlp.llp =
    DaggerSSet.freeCofibrations.{u} := by
  rw [llp_rlp_of_hasSmallObjectArgument.{u}]
  exact canonical_freeBoundarySaturation_eq

/-- Every original dagger arrow factors functorially in the exact original two classes. -/
def boundaryFactorizationData : DaggerSSet.freeCofibrations.{u}.FunctorialFactorizationData
    (freeBoundaryGenerators freeDagger.{u}).rlp := by
  rw [← boundary_rlp_llp_eq_freeCof]
  exact SmallObject.functorialFactorizationData _ Cardinal.aleph0.{u}

end

end DaggerOriginalFreeCofibrationGeneration
