import OriginalEC2BorelCofibrantObject
import OriginalEC2BorelModelCompatibility

/-!
# Canonical initial-arrow lifting for the actual realized EC₂ action

The realized zero skeleton is initial.  Transporting its verified lifting
property along the unique initial-object isomorphism gives the standard
`initial.to` map to the literal realized EC₂ action.
-/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open scoped TopCat.modelCategory
open DaggerOriginalDaggerRealizationC2Action DaggerOriginalEC2RealizationAction
open DaggerOriginalEC2BorelCofibrancy DaggerOriginalEC2BorelCofibrantObject
open DaggerOriginalEC2BorelModelCompatibility

universe u

namespace DaggerOriginalEC2CanonicalBorelCofibrancy

noncomputable section

/-- The canonical initial arrow to the actual realized EC₂ action has the
Borel left lifting property against underlying trivial fibrations. -/
theorem actualRealizedEC2_canonicalBorelCofibrant :
    borelCofibrations.{u} (initial.to realizedEC2Action.{u}) := by
  let e := initialIsoIsInitial (realizedSkeletalZeroIsInitial.{u})
  have h : (initial.to realizedEC2Action.{u}) =
      e.hom ≫ (realizedSkeletalZeroIsInitial.{u}).to realizedEC2Action.{u} :=
    initialIsInitial.hom_ext _ _
  rw [h]
  intro X Y p hp
  have he : HasLiftingProperty e.hom p := inferInstance
  have hc : HasLiftingProperty
      ((realizedSkeletalZeroIsInitial.{u}).to realizedEC2Action.{u}) p :=
    actualRealizedEC2_borelCofibrant.{u} p hp
  have : HasLiftingProperty e.hom p := he
  have : HasLiftingProperty
      ((realizedSkeletalZeroIsInitial.{u}).to realizedEC2Action.{u}) p := hc
  infer_instance

/-- Explicitly, every equivariant map whose underlying TopCat map is a
fibration and a weak equivalence admits lifts from the canonical initial
arrow to the original realized EC₂ action. -/
theorem actualRealizedEC2_lifts_trivialFibrations
    {X Y : Action TopCat.{u} C2.{u}} (p : X ⟶ Y)
    (hp : Fibration p.hom) (hw : WeakEquivalence p.hom) :
    HasLiftingProperty (initial.to realizedEC2Action.{u}) p :=
  actualRealizedEC2_canonicalBorelCofibrant.{u} p
    ((borelTrivialFibrations_iff p).2 ⟨hp, hw⟩)

end

end DaggerOriginalEC2CanonicalBorelCofibrancy
