import OriginalBorelGeneratorAcyclicity

/-!
# Original underlying weak equivalences and free-horn acyclicity

Weak equivalences are defined by the original underlying TopCat map. The
free-horn left lifting class lies in this class, including all countable
composites of pushouts of coproducts of the actual free-horn generators.
-/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MorphismProperty HomotopicalAlgebra
open scoped TopCat.modelCategory
open DaggerOriginalDaggerRealizationC2Action DaggerOriginalBorelFreeGenerators
open DaggerOriginalBorelGeneratorAcyclicity

universe u

namespace DaggerOriginalBorelWeakEquivalenceClasses

/-- The original Borel weak equivalences are detected by the literal underlying map. -/
def borelWeakEquivalences : MorphismProperty (Action TopCat.{u} C2.{u}) :=
  (weakEquivalences TopCat.{u}).inverseImage (Action.forget TopCat.{u} C2.{u})

/-- This class has the native two-out-of-three property. -/
instance : borelWeakEquivalences.{u}.HasTwoOutOfThreeProperty := by
  unfold borelWeakEquivalences
  infer_instance

/-- This class is stable under native categorical retracts. -/
instance : borelWeakEquivalences.{u}.IsStableUnderRetracts := by
  unfold borelWeakEquivalences
  infer_instance

/-- Membership is precisely the underlying native weak-equivalence assertion. -/
theorem borelWeakEquivalences_iff {X Y : Action TopCat.{u} C2.{u}} (p : X ⟶ Y) :
    borelWeakEquivalences p ↔ WeakEquivalence p.hom := by
  exact (weakEquivalence_iff p.hom).symm

/-- The complete free-horn left lifting class is acyclic for the original weak equivalences. -/
theorem J_rlp_llp_le_borelWeakEquivalences : J.{u}.rlp.llp ≤ borelWeakEquivalences.{u} := by
  intro X Y i hi
  exact (borelWeakEquivalences_iff i).2 (J_rlp_llp_underlying_weakEquivalence i hi)

/-- Countable free-horn cell composites are underlying weak equivalences. -/
theorem infiniteCompositions_J_le_borelWeakEquivalences :
    (coproducts.{u} J.{u}).pushouts.transfiniteCompositionsOfShape ℕ ≤
      borelWeakEquivalences.{u} := by
  have h : (coproducts.{u} J.{u}).pushouts ≤ J.{u}.rlp.llp :=
    (pushouts_monotone J.coproducts_le_llp_rlp).trans (MorphismProperty.pushouts_le)
  intro X Y f hf
  obtain ⟨hf⟩ := hf
  apply J_rlp_llp_le_borelWeakEquivalences
  exact (J.rlp.llp.transfiniteCompositionsOfShape_le ℕ) f ⟨hf.ofLE h⟩

/-- Within the original free-horn right class, free-boundary lifting is exactly acyclicity. -/
theorem fibration_is_trivial_iff {X Y : Action TopCat.{u} C2.{u}}
    (p : X ⟶ Y) (hp : J.rlp p) : I.rlp p ↔ borelWeakEquivalences p := by
  rw [I_rlp_iff_trivialFibration, borelWeakEquivalences_iff]
  exact and_iff_right ((J_rlp_iff_fibration p).1 hp)

end DaggerOriginalBorelWeakEquivalenceClasses
