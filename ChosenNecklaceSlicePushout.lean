import ChosenNecklaceSliceDesc
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs

open CategoryTheory Limits EnrichedCategory MonoidalCategory Opposite Simplicial

universe u

namespace DaggerChosenRigidificationNecklace.NecklaceThickening

noncomputable section

open NecklaceCode

variable (T : NecklaceCode) (j : Fin (T.len + 1))

def slicePointLeg (right : Bool) : NC.{u} point ⟶ slice.{u} T j right :=
  pointNCFunctor (slice T j right) (sliceJoint T j right)

theorem slicePoint_comm :
    slicePointLeg.{u} T j false ≫ sliceInclusion T j false =
      slicePointLeg T j true ≫ sliceInclusion T j true := by
  apply pointNCFunctor_ext
  rfl

/-- The actual point-gluing cocone, with both original full-Hom inclusions. -/
def sliceCocone : PushoutCocone (slicePointLeg.{u} T j false) (slicePointLeg T j true) :=
  PushoutCocone.mk (sliceInclusion T j false) (sliceInclusion T j true) (slicePoint_comm T j)

/-- Full arbitrary-target enriched UP, retaining desc, both fac and arbitrary whole-functor uniq. -/
def sliceCoconeIsColimit (hj : j ∈ T.joints) : IsColimit (sliceCocone.{u} T j) := by
  apply PushoutCocone.isColimitAux'
  intro s
  have h : s.inl.obj (sliceJoint T j false) = s.inr.obj (sliceJoint T j true) :=
    congrArg (fun L ↦ L.obj pointObj) s.condition
  refine ⟨sliceDesc j hj s.inl s.inr h, sliceDesc_left j hj s.inl s.inr h,
    sliceDesc_right j hj s.inl s.inr h, ?_⟩
  intro m hm0 hm1
  exact sliceDesc_uniq j hj s.inl s.inr h m hm0 hm1

theorem sliceIsPushout (hj : j ∈ T.joints) :
    IsPushout (slicePointLeg.{u} T j false) (slicePointLeg T j true)
      (sliceInclusion T j false) (sliceInclusion T j true) :=
  IsPushout.of_isColimit (sliceCoconeIsColimit T j hj)

end

end DaggerChosenRigidificationNecklace.NecklaceThickening
