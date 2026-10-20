import OriginalFixedObjectDaggerAccessibleInclusion
import OriginalAdjunctionSmallMappedGenerators
import FixedCategoryFilteredDomains

/-!
# Actual small generating families and finite presentability after original completion

Keep the literal images of every legacy boundary and horn generator. The inclusion's
proved accessibility transfers the already proved finite presentability of their domains.
The right lifting classes remain the exact original Homwise classes.
-/
set_option autoImplicit false
open CategoryTheory DaggerModels
open DaggerOriginalFixedObjectDaggerCategories DaggerOriginalFixedObjectGroupoidClasses
open DaggerOriginalFixedObjectStrictDaggerGenerators
open DaggerOriginalAdjunctionSmallMappedGenerators
universe u
namespace DaggerOriginalFixedObjectStrictDaggerSmallness
noncomputable section
attribute [local instance] Cardinal.fact_isRegular_aleph0

/-- Literal original completion images of the legacy boundary generating family. -/
def boundaryGenerators (O : Type u) : MorphismProperty (FixedStrictDaggerGroupoids O) :=
  mappedFamilyClass (DaggerFixedCategoryGenerators.I O) (legacyStrictCompletion O)

/-- Literal original completion images of the legacy horn generating family. -/
def hornGenerators (O : Type u) : MorphismProperty (FixedStrictDaggerGroupoids O) :=
  mappedFamilyClass (DaggerFixedCategoryGenerators.J O) (legacyStrictCompletion O)

/-- The actual boundary image family is small in the original universe. -/
instance boundaryGenerators_isSmall (O : Type u) :
    MorphismProperty.IsSmall.{u} (boundaryGenerators O) := by
  letI := DaggerFixedCategoryGenerators.I_isSmall O
  unfold boundaryGenerators
  infer_instance

/-- The actual horn image family is small in the original universe. -/
instance hornGenerators_isSmall (O : Type u) :
    MorphismProperty.IsSmall.{u} (hornGenerators O) := by
  letI := DaggerFixedCategoryGenerators.J_isSmall O
  unfold hornGenerators
  infer_instance

/-- These small boundary generators detect exactly the intended original trivial fibrations. -/
theorem boundaryGenerators_rlp_eq (O : Type u) :
    (boundaryGenerators O).rlp = strictDaggerFibrations O ⊓ strictDaggerWeakEquivalences O := by
  rw [boundaryGenerators, mappedFamilyClass_rlp_eq (legacyStrictAdjunction O),
    ← DaggerOriginalAdjunctionMappedLifting.mapped_rlp_eq (legacyStrictAdjunction O)]
  exact strictI_rlp_eq O

/-- These small horn generators detect exactly the intended original fibrations. -/
theorem hornGenerators_rlp_eq (O : Type u) :
    (hornGenerators O).rlp = strictDaggerFibrations O := by
  rw [hornGenerators, mappedFamilyClass_rlp_eq (legacyStrictAdjunction O),
    ← DaggerOriginalAdjunctionMappedLifting.mapped_rlp_eq (legacyStrictAdjunction O)]
  exact strictJ_rlp_eq O

/-- Each actual completed boundary generator has a finitely presentable original domain. -/
theorem boundary_domain_isFinitelyPresentable (O : Type u) {A B : FixedStrictDaggerGroupoids O}
    (i : A ⟶ B) (hi : boundaryGenerators O i) : IsFinitelyPresentable.{u} A := by
  rcases hi with ⟨a⟩
  haveI : IsFinitelyPresentable.{u} a.1.left :=
    DaggerFixedCategoryFilteredDomains.I_domain_isFinitelyPresentable O a.1.hom a.2
  exact (legacyStrictAdjunction O).isCardinalPresentable_leftAdjoint_obj
    Cardinal.aleph0.{u} a.1.left

/-- Each actual completed horn generator has a finitely presentable original domain. -/
theorem horn_domain_isFinitelyPresentable (O : Type u) {A B : FixedStrictDaggerGroupoids O}
    (i : A ⟶ B) (hi : hornGenerators O i) : IsFinitelyPresentable.{u} A := by
  rcases hi with ⟨a⟩
  haveI : IsFinitelyPresentable.{u} a.1.left :=
    DaggerFixedCategoryFilteredDomains.J_domain_isFinitelyPresentable O a.1.hom a.2
  exact (legacyStrictAdjunction O).isCardinalPresentable_leftAdjoint_obj
    Cardinal.aleph0.{u} a.1.left

end
end DaggerOriginalFixedObjectStrictDaggerSmallness
