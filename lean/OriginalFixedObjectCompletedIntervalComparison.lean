import OriginalFixedObjectDaggerDerivedCompletion
import OriginalFixedObjectFreePointInterval
import OriginalCofibrantReplacementComparisonChallengeProof

/-!
# Completion of the original ambient interval and comparison over I_dagger

The extension is the actual completion adjunction applied to the original dagger
functor. Its triangle retains every original Hom and fixed endpoint. If the actual
localization unit is a weak equivalence, two-out-of-three gives a weak completed
augmentation. That DK80 hypothesis remains explicit and is not proved here.
For a cofibrant ambient source, the actual completed source and F01(EC2) have weak
comparison maps in both directions, each over the exact original interval.
-/
set_option autoImplicit false
open CategoryTheory Limits HomotopicalAlgebra
open DaggerOriginalFixedObjectDaggerCategories DaggerOriginalFixedObjectGroupoidCompletionAdjunction
open DaggerOriginalFixedObjectDaggerCompletionQuillen
open DaggerOriginalFixedObjectDaggerDerivedCompletion
open DaggerOriginalFixedObjectOrdinaryCellAdjunction
open DaggerOriginalFixedObjectGroupoidTerminals
open DaggerOriginalFixedObjectFreePointInterval DaggerOriginalFreeEC2DaggerGroupoidComparison
open scoped DaggerOriginalFixedObjectGroupoidClasses DaggerOriginalFixedObjectCofibrations
  DaggerOriginalFixedObjectStrictDaggerModel DaggerOriginalFixedObjectAmbientDaggerModel
universe u
namespace DaggerOriginalFixedObjectCompletedIntervalComparison
noncomputable section

/-- The full original completion extension into any strict dagger target. -/
def completedExtension {O : Type u} {H : FixedDaggerCategory O}
    {T : FixedStrictDaggerGroupoids O} (f : H ⟶ T.obj) :
    (fixedDaggerCompletion O).obj H ⟶ T :=
  (fixedDaggerCompletionHomEquiv H T).symm f

/-- The original localization triangle commutes as an equality of whole dagger functors. -/
theorem completedExtension_triangle {O : Type u} {H : FixedDaggerCategory O}
    {T : FixedStrictDaggerGroupoids O} (f : H ⟶ T.obj) :
    fixedDaggerLocalization H ≫ (completedExtension f).hom = f :=
  (fixedDaggerCompletionHomEquiv H T).apply_symm_apply f

/-- The local-equivalence input is exactly the original localization unit, kept explicit. -/
theorem completedExtension_weakEquivalence {O : Type u} {H : FixedDaggerCategory O}
    {T : FixedStrictDaggerGroupoids O} (f : H ⟶ T.obj)
    [WeakEquivalence f] [WeakEquivalence (fixedDaggerLocalization H)] :
    WeakEquivalence (completedExtension f) := by
  apply (inclusion_weakEquivalence_iff (completedExtension f)).1
  have : WeakEquivalence (fixedDaggerLocalization H ≫ (completedExtension f).hom) := by
    rw [completedExtension_triangle]
    infer_instance
  exact weakEquivalence_of_precomp (fixedDaggerLocalization H) (completedExtension f).hom

/-- Complete the actual ambient approximation to the paper's literal unitary interval. -/
def completedAugmentation {H : FixedDaggerCategory TwoObjects.{u}}
    (f : H ⟶ unitaryInterval.obj) :
    (fixedDaggerCompletion TwoObjects).obj H ⟶ unitaryInterval := completedExtension f

/-- The completed augmentation has the original ambient augmentation as its unit triangle. -/
theorem completedAugmentation_triangle {H : FixedDaggerCategory TwoObjects.{u}}
    (f : H ⟶ unitaryInterval.obj) :
    fixedDaggerLocalization H ≫ (completedAugmentation f).hom = f :=
  completedExtension_triangle f

/-- Every actual strict source is fibrant and the actual interval is terminal. -/
theorem completedAugmentation_fibration {H : FixedDaggerCategory TwoObjects.{u}}
    (f : H ⟶ unitaryInterval.obj) : Fibration (completedAugmentation f) :=
  (isFibrant_iff_of_isTerminal (completedAugmentation f)
    (strictDaggerTerminalIsTerminal TwoObjects)).1 inferInstance

/-- The completed original approximation is trivial fibrant once the DK80 unit input holds. -/
theorem completedAugmentation_trivialFibration {H : FixedDaggerCategory TwoObjects.{u}}
    (f : H ⟶ unitaryInterval.obj)
    [WeakEquivalence f] [WeakEquivalence (fixedDaggerLocalization H)] :
    trivialFibrations (FixedStrictDaggerGroupoids TwoObjects) (completedAugmentation f) :=
  (mem_trivialFibrations_iff _).2
    ⟨completedAugmentation_fibration f, completedExtension_weakEquivalence f⟩

/-- A cofibrant ambient interval has a weak comparison to the actual free EC2 over I_dagger. -/
theorem exists_completedToFree {H : FixedDaggerCategory TwoObjects.{u}}
    (f : H ⟶ unitaryInterval.obj) [IsCofibrant H]
    [WeakEquivalence f] [WeakEquivalence (fixedDaggerLocalization H)] :
    ∃ l : (fixedDaggerCompletion TwoObjects).obj H ⟶ freeEC2,
      l ≫ augmentation = completedAugmentation f ∧ WeakEquivalence l :=
  DaggerOriginalCofibrantReplacementComparisonChallengeProof.challengeProof
    (FixedStrictDaggerGroupoids TwoObjects) _ _ _ (completion_isCofibrant H)
    (completedAugmentation f) augmentation (completedExtension_weakEquivalence f)
    augmentation_fibration augmentation_weakEquivalence

/-- Choose the whole original comparison, keeping its exact triangle and weak class below. -/
def completedToFree {H : FixedDaggerCategory TwoObjects.{u}}
    (f : H ⟶ unitaryInterval.obj) [IsCofibrant H]
    [WeakEquivalence f] [WeakEquivalence (fixedDaggerLocalization H)] :
    (fixedDaggerCompletion TwoObjects).obj H ⟶ freeEC2 :=
  Classical.choose (exists_completedToFree f)

/-- The chosen comparison commutes with the exact two interval augmentations. -/
theorem completedToFree_triangle {H : FixedDaggerCategory TwoObjects.{u}}
    (f : H ⟶ unitaryInterval.obj) [IsCofibrant H]
    [WeakEquivalence f] [WeakEquivalence (fixedDaggerLocalization H)] :
    completedToFree f ≫ augmentation = completedAugmentation f :=
  (Classical.choose_spec (exists_completedToFree f)).1

/-- The chosen comparison is weak on all four actual original simplicial Hom objects. -/
theorem completedToFree_weakEquivalence {H : FixedDaggerCategory TwoObjects.{u}}
    (f : H ⟶ unitaryInterval.obj) [IsCofibrant H]
    [WeakEquivalence f] [WeakEquivalence (fixedDaggerLocalization H)] :
    WeakEquivalence (completedToFree f) :=
  (Classical.choose_spec (exists_completedToFree f)).2

/-- The actual free EC2 also admits a weak comparison back over precisely the same interval. -/
theorem exists_freeToCompleted {H : FixedDaggerCategory TwoObjects.{u}}
    (f : H ⟶ unitaryInterval.obj)
    [WeakEquivalence f] [WeakEquivalence (fixedDaggerLocalization H)] :
    ∃ l : freeEC2 ⟶ (fixedDaggerCompletion TwoObjects).obj H,
      l ≫ completedAugmentation f = augmentation ∧ WeakEquivalence l :=
  DaggerOriginalCofibrantReplacementComparisonChallengeProof.challengeProof
    (FixedStrictDaggerGroupoids TwoObjects) _ _ _ augmentation_source_isCofibrant
    augmentation (completedAugmentation f) augmentation_weakEquivalence
    (completedAugmentation_fibration f) (completedExtension_weakEquivalence f)

/-- Choose the actual full reverse comparison without asserting a strict inverse. -/
def freeToCompleted {H : FixedDaggerCategory TwoObjects.{u}}
    (f : H ⟶ unitaryInterval.obj)
    [WeakEquivalence f] [WeakEquivalence (fixedDaggerLocalization H)] :
    freeEC2 ⟶ (fixedDaggerCompletion TwoObjects).obj H :=
  Classical.choose (exists_freeToCompleted f)

/-- The reverse comparison has the literal original augmentation triangle. -/
theorem freeToCompleted_triangle {H : FixedDaggerCategory TwoObjects.{u}}
    (f : H ⟶ unitaryInterval.obj)
    [WeakEquivalence f] [WeakEquivalence (fixedDaggerLocalization H)] :
    freeToCompleted f ≫ completedAugmentation f = augmentation :=
  (Classical.choose_spec (exists_freeToCompleted f)).1

/-- The reverse comparison is a weak equivalence of the full original strict dagger groupoids. -/
theorem freeToCompleted_weakEquivalence {H : FixedDaggerCategory TwoObjects.{u}}
    (f : H ⟶ unitaryInterval.obj)
    [WeakEquivalence f] [WeakEquivalence (fixedDaggerLocalization H)] :
    WeakEquivalence (freeToCompleted f) :=
  (Classical.choose_spec (exists_freeToCompleted f)).2

end
end DaggerOriginalFixedObjectCompletedIntervalComparison
