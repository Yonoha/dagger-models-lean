import OriginalAmbientDaggerIntervalComponents

/-!
# Inverses of original interval vertices on actual Hom components

The original dagger of each actual vertex is an inverse after passing to the
actual component sets. Both inverse identities use the original enriched
composition and identity; no replacement Hom sets or composition are used.
This is the pointwise inverse condition needed for the pi0 groupoid input,
not a proof of the localization unit or the general pi0-category construction.
-/
set_option autoImplicit false
open CategoryTheory MonoidalCategory HomotopicalAlgebra Opposite Simplicial
open DaggerOriginalFixedObjectDaggerCategories DaggerOriginalFixedObjectGroupoidTerminals
open DaggerOriginalAmbientDaggerIntervalComponents
open scoped SSet.modelCategoryQuillen DaggerOriginalFixedObjectAmbientDaggerModel
universe u
namespace DaggerOriginalAmbientIntervalPiZeroDaggerInverse

/-- The actual dagger vertex satisfies both inverse equations in the original Hom components. -/
theorem vertexDagger_inverse_components {O : Type u} {H : FixedDaggerCategory O}
    (f : H ⟶ terminalFixedDagger O) [WeakEquivalence f] (x y : O)
    (a : (H.underlying.enriched.Hom x y).obj (op ⦋0⦌)) :
    SSet.π₀.mk ((H.underlying.enriched.comp x y x).app (op ⦋0⦌)
        (a, (H.dagger.dagger x y).app (op ⦋0⦌) a)) =
      SSet.π₀.mk ((H.underlying.enriched.id x).app (op ⦋0⦌) PUnit.unit) ∧
    SSet.π₀.mk ((H.underlying.enriched.comp y x y).app (op ⦋0⦌)
        ((H.dagger.dagger x y).app (op ⦋0⦌) a, a)) =
      SSet.π₀.mk ((H.underlying.enriched.id y).app (op ⦋0⦌) PUnit.unit) := by
  have := homComponents_subsingleton f x x
  have := homComponents_subsingleton f y y
  exact ⟨Subsingleton.elim _ _, Subsingleton.elim _ _⟩

end DaggerOriginalAmbientIntervalPiZeroDaggerInverse
