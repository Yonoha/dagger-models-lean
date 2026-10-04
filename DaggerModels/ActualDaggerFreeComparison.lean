import DaggerModels.DaggerFreeComparison
import DaggerModels.OrdinaryFreeDagger

/-!
# The actual free-functor comparison in Part I `dj.lem.lift`

The required ordinary-category free dagger adjunction has now been constructed.
The comparison reuses Mathlib's canonical mate of the identity common right
functor and preserves both composite adjunction structures.
-/

open CategoryTheory

universe u

noncomputable section

namespace DaggerModels.OrdinaryRigidification.DaggerFreeComparison

open DaggerNerve DaggerRigidification DaggerAdjunction

/-- The target composite uses the actual ordinary-category free dagger adjunction. -/
def canonicalTargetAdjunction :
    rigidification.{u} ⋙ OrdinaryFreeDagger.functor ⊣
      DaggerSimplicialCat.forget ⋙ coherentNerve :=
  targetAdjunction OrdinaryFreeDagger.adjunction

/-- The actual natural comparison, without an assumed or postulated free adjunction. -/
def canonicalFreeComparison :
    freeDagger.{u} ⋙ daggerRigidification ≅ rigidification ⋙ OrdinaryFreeDagger.functor :=
  freeComparison OrdinaryFreeDagger.adjunction

/-- The comparison preserves the entire actual composite unit. -/
theorem canonicalFreeComparison_unit (X : SSet.{u}) :
    sourceAdjunction.unit.app X ≫
        (DaggerSimplicialCat.forget ⋙ coherentNerve).map
          (canonicalFreeComparison.hom.app X) =
      canonicalTargetAdjunction.unit.app X :=
  freeComparison_unit OrdinaryFreeDagger.adjunction X

/-- The comparison preserves the entire enriched composite counit. -/
theorem canonicalFreeComparison_counit (C : DaggerSimplicialCat.{u, u}) :
    canonicalFreeComparison.hom.app (coherentNerve.obj C.toSimplicialCat) ≫
        canonicalTargetAdjunction.counit.app C =
      sourceAdjunction.counit.app C :=
  freeComparison_counit OrdinaryFreeDagger.adjunction C

/-- It is exactly the canonical mate specified in the manuscript proof. -/
theorem canonicalFreeComparison_mate (X : SSet.{u}) :
    sourceAdjunction.homEquiv X ((rigidification ⋙ OrdinaryFreeDagger.functor).obj X)
        (canonicalFreeComparison.hom.app X) =
      canonicalTargetAdjunction.unit.app X :=
  freeComparison_mate OrdinaryFreeDagger.adjunction X

/-- All conclusions of the lifted-adjunction lemma for the original actual functors. -/
theorem lifted_adjunction_and_free_comparison :
    Nonempty (daggerRigidification.{u} ⊣ daggerCoherentNerve) ∧
      daggerRigidification ⋙ DaggerSimplicialCat.forget = DaggerSSet.forget ⋙ rigidification ∧
      daggerCoherentNerve ⋙ DaggerSSet.forget = DaggerSimplicialCat.forget ⋙ coherentNerve ∧
      Nonempty (freeDagger ⋙ daggerRigidification ≅ rigidification ⋙ OrdinaryFreeDagger.functor) :=
  ⟨⟨daggerRigidificationCoherentNerveAdjunction⟩, daggerRigidification_forget,
    daggerCoherentNerve_forget, ⟨canonicalFreeComparison⟩⟩

end DaggerModels.OrdinaryRigidification.DaggerFreeComparison
