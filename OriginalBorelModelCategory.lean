import OriginalBorelFiniteSourceSmallness
import OriginalEC2CanonicalBorelCofibrancy

/-!
# The actual Borel model structure on topological C₂ actions

The native TopPackage is instantiated using free realized boundaries and horns,
finite free realization sources, and the proved original underlying weak
equivalences. The resulting model structure has exactly the original Borel
cofibrations and underlying native TopCat fibrations and weak equivalences.
-/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MorphismProperty HomotopicalAlgebra
open scoped TopCat.modelCategory
open DaggerOriginalDaggerRealizationC2Action DaggerOriginalBorelFreeGenerators
open DaggerOriginalBorelWeakEquivalenceClasses DaggerOriginalBorelFiniteSourceSmallness
open DaggerOriginalEC2BorelCofibrancy DaggerOriginalEC2BorelModelCompatibility

universe u

namespace DaggerOriginalBorelModelCategory

noncomputable section

/-- Native weak-equivalence data, detected on the literal underlying topological map. -/
scoped instance weakStructure : CategoryWithWeakEquivalences (Action TopCat.{u} C2.{u}) where
  weakEquivalences := borelWeakEquivalences

/-- Native cofibration data, using the original Borel left lifting class. -/
scoped instance cofStructure : CategoryWithCofibrations (Action TopCat.{u} C2.{u}) where
  cofibrations := borelCofibrations

/-- Native fibration data, using the actual free-horn right lifting class. -/
scoped instance fibStructure : CategoryWithFibrations (Action TopCat.{u} C2.{u}) where
  fibrations := J.rlp

open scoped DaggerOriginalBorelModelCategory

/-- The full native model package, with every construction condition proved. -/
def packageBorel : TopPackage.{u} (Action TopCat.{u} C2.{u}) where
  I' := I
  J' := J
  S' := Set.range (fun (T : {T : SSet.{u} | SSet.IsFinite T}) ↦
    free.obj (SSet.toTop.obj T.val))
  hasTwoOutOfThreeProperty := inferInstanceAs borelWeakEquivalences.HasTwoOutOfThreeProperty
  isStableUnderRetracts := inferInstanceAs borelWeakEquivalences.IsStableUnderRetracts
  rlp_I'_le_rlp_J' := I_rlp_le_J_rlp
  fibration_is_trivial_iff' := by
    intro X Y p hp
    rw [weakEquivalence_iff]
    exact fibration_is_trivial_iff p hp
  src_I_le_S' := by
    rintro A B i ⟨n⟩
    exact ⟨⟨SSet.boundary n, by
      change SSet.IsFinite (SSet.boundary n : SSet.{u})
      infer_instance⟩, rfl⟩
  src_J_le_S' := by
    intro A B i hi
    simp only [J, iSup_iff] at hi
    obtain ⟨n, ⟨k⟩⟩ := hi
    exact ⟨⟨SSet.horn (n + 1) k, by
      change SSet.IsFinite (SSet.horn (n + 1) k : SSet.{u})
      infer_instance⟩, rfl⟩
  infiniteCompositions_le_W' := infiniteCompositions_J_le_borelWeakEquivalences
  preservesColimit' := by
    rintro A ⟨⟨T, hT⟩, rfl⟩ X Y f hf
    have : SSet.IsFinite T := hT
    exact finiteFreeSource_preservesColimit T f hf

/-- The full Borel model structure on the literal action category. -/
scoped instance modelStructure : ModelCategory (Action TopCat.{u} C2.{u}) :=
  packageBorel.modelCategory (by
    change borelCofibrations = I.rlp.llp
    exact I_rlp_llp_eq_borelCofibrations.symm) rfl

/-- Native action weak equivalences are exactly the underlying native TopCat weak equivalences. -/
theorem weakEquivalence_iff_underlying {X Y : Action TopCat.{u} C2.{u}} (p : X ⟶ Y) :
    WeakEquivalence p ↔ WeakEquivalence p.hom := by
  rw [weakEquivalence_iff]
  exact borelWeakEquivalences_iff p

/-- Native action fibrations are exactly the underlying native TopCat fibrations. -/
theorem fibration_iff_underlying {X Y : Action TopCat.{u} C2.{u}} (p : X ⟶ Y) :
    Fibration p ↔ Fibration p.hom := by
  rw [fibration_iff]
  exact J_rlp_iff_fibration p

/-- Native action cofibrations are exactly the original Borel cofibration class. -/
theorem cofibration_iff_original {X Y : Action TopCat.{u} C2.{u}} (p : X ⟶ Y) :
    Cofibration p ↔ borelCofibrations p := by
  rw [cofibration_iff]
  rfl

/-- The native trivial-fibration class is the original Borel right lifting class. -/
theorem trivialFibrations_eq_original :
    trivialFibrations (Action TopCat.{u} C2.{u}) = borelTrivialFibrations.{u} := by
  ext X Y p
  rw [mem_trivialFibrations_iff, borelTrivialFibrations_iff,
    fibration_iff_underlying, weakEquivalence_iff_underlying]

end

end DaggerOriginalBorelModelCategory
