import ActualQWeightedCarrierColimits

/-! Transfer the native coordinate colimits to the unchanged entire Q-weighted resolution. -/
set_option autoImplicit false
open CategoryTheory Limits Opposite
open DaggerActualQWeightedResolutionCells DaggerActualQWeightedCarrierColimits
universe u
namespace DaggerActualQWeightedResolutionColimits
noncomputable section

/-- The entire original resolution, evaluated in a degree, has the proved cell coordinates. -/
def carrierIso (q : SimplexCategoryᵒᵖ) :
    DaggerActualQWeightedResolutionFunctor.functor.{u} ⋙
      (evaluation SimplexCategoryᵒᵖ (Type u)).obj q ≅ carrier q q :=
  NatIso.ofComponents (fun X ↦
    { hom := fun x ↦ flatEquiv X q q x
      inv := fun x ↦ (flatEquiv X q q).symm x
      hom_inv_id := by funext x; exact (flatEquiv X q q).left_inv x
      inv_hom_id := by funext x; exact (flatEquiv X q q).right_inv x }) (by
        intro X Y f
        funext x
        exact flatEquiv_naturality f q q x)

/-- Native evaluation jointly detects colimits of the original full simplicial-set functor. -/
instance functor_preservesColimit {J : Type u} [Category.{u} J] (D : J ⥤ SSet.{u}) :
    PreservesColimit D DaggerActualQWeightedResolutionFunctor.functor.{u} := by
  apply preservesColimit_of_evaluation DaggerActualQWeightedResolutionFunctor.functor D
  intro q
  exact preservesColimit_of_natIso D (carrierIso q).symm

/-- All colimits of the original universe are preserved, with unchanged objects and maps. -/
instance functor_preservesColimits :
    PreservesColimitsOfSize.{u, u} DaggerActualQWeightedResolutionFunctor.functor.{u} where
  preservesColimitsOfShape := by
    intro J hJ
    constructor
    intro D
    infer_instance

end
end DaggerActualQWeightedResolutionColimits
