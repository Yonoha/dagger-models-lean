import ActualTaggedWalkingIsoSourceHomotopyReconciled
import OriginalNerveProduct

/-!
# The literal walking vertex inclusion is the nerve of an ordinary equivalence

Use Mathlib's actual standard-simplex nerve isomorphism and ordinary equivalence
structure. This is categorical data for the original walking generator; it
asserts no Joyal or DCH model structure and no replacement of their weak classes.
-/
set_option autoImplicit false
open CategoryTheory Simplicial Opposite DaggerModels
open DaggerModels.OriginalWalkingIsoIntegerObstruction
open DaggerActualFreeWalkingIsoIntegerObstruction
open DaggerActualTaggedWalkingIsoSourceHomotopy
universe u
namespace DaggerActualWalkingIsoCategoricalEquivalence
noncomputable section

/-- The exact finite ordinal appearing in the native zero-simplex nerve isomorphism. -/
abbrev pointCategory := ULift.{u} (Fin 1)

/-- The ordinary functor selects the original walking zero object. -/
def pointToWalking : pointCategory.{u} ⥤ walkingIso.{u} :=
  (Functor.const pointCategory.{u}).obj walkingZero

/-- The inverse ordinary functor takes every walking object to the sole point. -/
def walkingToPoint : walkingIso.{u} ⥤ pointCategory.{u} :=
  (Functor.const walkingIso.{u}).obj ⟨0⟩

/-- The point composite is isomorphic to the identity on the actual finite ordinal. -/
def unitIso : 𝟭 pointCategory.{u} ≅ pointToWalking.{u} ⋙ walkingToPoint.{u} :=
  NatIso.ofComponents (fun x ↦ eqToIso (Subsingleton.elim x _))
    (fun _ ↦ Subsingleton.elim _ _)

/-- The unique walking isomorphisms give the counit on every original object. -/
def counitIso : walkingToPoint.{u} ⋙ pointToWalking.{u} ≅ 𝟭 walkingIso.{u} :=
  NatIso.ofComponents (fun _ ↦
    { hom := ⟨⟨⟩⟩
      inv := ⟨⟨⟩⟩
      hom_inv_id := rfl
      inv_hom_id := rfl })
    (fun _ ↦ rfl)

/-- An actual Mathlib equivalence, retaining the specified forward functor. -/
def pointEquivalence : pointCategory.{u} ≌ walkingIso.{u} :=
  CategoryTheory.Equivalence.mk pointToWalking walkingToPoint unitIso counitIso

/-- The specified forward functor is an ordinary categorical equivalence. -/
instance pointToWalking_isEquivalence : pointToWalking.{u}.IsEquivalence :=
  show pointEquivalence.{u}.functor.IsEquivalence by infer_instance

/-- Its nerve is literally the old zero-vertex inclusion, after the native source isomorphism. -/
theorem nerve_pointToWalking :
    (SSet.stdSimplex.isoNerve.{u} 0).hom ≫ nerveMap pointToWalking.{u} =
      zeroInclusion.{u} := by
  apply NatTrans.ext
  funext n s
  apply CategoryTheory.Functor.ext (fun _ ↦ rfl)

/-- The inverse nerve is literally the old collapse, after the same source identification. -/
theorem nerve_walkingToPoint :
    nerveMap walkingToPoint.{u} ≫ (SSet.stdSimplex.isoNerve.{u} 0).inv =
      collapse.{u} :=
  SSet.stdSimplex.isTerminalObj₀.hom_ext _ _

end
end DaggerActualWalkingIsoCategoricalEquivalence
