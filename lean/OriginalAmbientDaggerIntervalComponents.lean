import OriginalSimplicialPiZeroWeakEquivalence
import OriginalFixedObjectGroupoidTerminals

/-!
# Original Hom components of a weak approximation to the actual dagger interval

For every fixed object type, a Homwise weak equivalence to the actual singleton-
Hom terminal dagger has a singleton set of components on every original Hom.
No Kan hypothesis on the original Homs is used. This supplies the component
sets needed for the interval's pi0 groupoid input; it does not prove the DK80
localization theorem or construct the general pi0 category functor.
-/
set_option autoImplicit false
open CategoryTheory MonoidalCategory HomotopicalAlgebra
open DaggerOriginalFixedObjectDaggerCategories DaggerOriginalFixedObjectGroupoidTerminals
open DaggerOriginalFixedObjectAmbientDaggerModel
open DaggerOriginalSimplicialPiZeroWeakEquivalence
open scoped SSet.modelCategoryQuillen DaggerOriginalFixedObjectAmbientDaggerModel
universe u
namespace DaggerOriginalAmbientDaggerIntervalComponents
noncomputable section

/-- The components of the literal simplicial point coincide, by native vertex surjectivity. -/
theorem pointComponents_subsingleton : Subsingleton (𝟙_ SSet.{u}).π₀ := by
  refine ⟨fun a b ↦ ?_⟩
  obtain ⟨v, rfl⟩ := SSet.π₀.mk_surjective a
  obtain ⟨w, rfl⟩ := SSet.π₀.mk_surjective b
  have hvw : v = w := by
    cases v
    cases w
    rfl
  exact congrArg SSet.π₀.mk hvw

/-- All actual components of each original interval Hom coincide, without original Kan input. -/
theorem homComponents_subsingleton {O : Type u} {H : FixedDaggerCategory O}
    (f : H ⟶ terminalFixedDagger O) [WeakEquivalence f] (x y : O) :
    Subsingleton (H.underlying.enriched.Hom x y).π₀ := by
  have : WeakEquivalence (f.underlying.map x y) :=
    ((weakEquivalence_iff_original f).1 inferInstance) x y
  have hb := bijective_mapPiZero (f.underlying.map x y)
  have : Subsingleton ((terminalFixedDagger O).underlying.enriched.Hom x y).π₀ :=
    pointComponents_subsingleton
  refine ⟨fun a b ↦ hb.1 ?_⟩
  apply Subsingleton.elim

/-- Every original interval Hom has an actual component, including the off-diagonal Homs. -/
theorem homComponents_nonempty {O : Type u} {H : FixedDaggerCategory O}
    (f : H ⟶ terminalFixedDagger O) [WeakEquivalence f] (x y : O) :
    Nonempty (H.underlying.enriched.Hom x y).π₀ := by
  have : WeakEquivalence (f.underlying.map x y) :=
    ((weakEquivalence_iff_original f).1 inferInstance) x y
  obtain ⟨a, _⟩ := (bijective_mapPiZero (f.underlying.map x y)).2
    (SSet.π₀.mk (X := 𝟙_ SSet.{u}) PUnit.unit)
  exact ⟨a⟩

/-- The exact component set of every original Hom is a singleton. -/
def homComponents_unique {O : Type u} {H : FixedDaggerCategory O}
    (f : H ⟶ terminalFixedDagger O) [WeakEquivalence f] (x y : O) :
    Unique (H.underlying.enriched.Hom x y).π₀ := by
  have := homComponents_subsingleton f x y
  have := homComponents_nonempty f x y
  exact { default := Classical.choice (homComponents_nonempty f x y)
          uniq := fun _ ↦ Subsingleton.elim _ _ }

end
end DaggerOriginalAmbientDaggerIntervalComponents
