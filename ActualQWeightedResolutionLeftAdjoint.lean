import ActualQWeightedResolutionColimits

/-! Apply the native presheaf adjoint theorem to the unchanged Q-weighted resolution. -/
set_option autoImplicit false
open CategoryTheory Limits Opposite
universe u
namespace DaggerActualQWeightedResolutionLeftAdjoint
noncomputable section

/-- Native size shrinking supplies the small-hom colimits required by the presheaf theorem. -/
instance functor_preservesSmallHomColimits :
    PreservesColimitsOfSize.{0, u} DaggerActualQWeightedResolutionFunctor.functor.{u} :=
  preservesColimitsOfSize_shrink.{u, 0, 0, u} DaggerActualQWeightedResolutionFunctor.functor

/-- Colimit preservation gives left adjointness of the exact original resolution functor. -/
instance functor_isLeftAdjoint :
    DaggerActualQWeightedResolutionFunctor.functor.{u}.IsLeftAdjoint := by
  have : PreservesColimitsOfSize.{0, u}
      DaggerActualQWeightedResolutionFunctor.functor.{u} := functor_preservesSmallHomColimits
  exact Presheaf.isLeftAdjoint_of_preservesColimits.{u, 0, u, 0, u + 1}
    (C := SimplexCategoryᵒᵖ) (ℰ := SSet.{u}) DaggerActualQWeightedResolutionFunctor.functor

end
end DaggerActualQWeightedResolutionLeftAdjoint
