import FixedGraphHomwise
import IinjBridge

/-!
# The actual geometric weak-equivalence class under graph decomposition

The imported Kan–Quillen structure uses realization followed by the singular
Kan complex. Its existing isomorphism stability supplies the generic premise.
No graph model structure or source/target Kan condition is assumed here.
-/

open CategoryTheory HomotopicalAlgebra DaggerModels
open scoped SSet.modelCategoryQuillen

universe u

namespace DaggerFixedGraph

variable {O : Type u} [LinearOrder O] {G H : FixedDaggerSimplicialGraph O}

/-- The original geometric weak-equivalence class is detected by the actual factors. -/
theorem weak_equivalence_iff_factors (f : G ⟶ H) :
    (∀ x y : O, WeakEquivalence (f.map x y)) ↔
      (∀ p : Upper O, WeakEquivalence (((decomposition (O := O)).functor.map f).1 p)) ∧
        (∀ x : O,
          WeakEquivalence ((((decomposition (O := O)).functor.map f).2 x).app PUnit.unit)) := by
  simpa only [HomotopicalAlgebra.weakEquivalence_iff] using
    homwise_iff_factors (weakEquivalences SSet.{u}) f

/-- Expose exactly the realization/singular-Kan definition, on every original hom. -/
theorem geometric_weak_equivalence_iff_factors (f : G ⟶ H) :
    (∀ x y : O, SSet.KanComplex.W (TopCat.toSSet.map (SSet.toTop.map (f.map x y)))) ↔
      (∀ p : Upper O, SSet.KanComplex.W (TopCat.toSSet.map
        (SSet.toTop.map (((decomposition (O := O)).functor.map f).1 p)))) ∧
      (∀ x : O, SSet.KanComplex.W (TopCat.toSSet.map
        (SSet.toTop.map ((((decomposition (O := O)).functor.map f).2 x).app PUnit.unit)))) := by
  simpa only [KanQuillenReuse.weakEquivalence_iff_geometric] using
    weak_equivalence_iff_factors f

end DaggerFixedGraph

namespace DaggerFixedGraph

/-- The exact geometric property on all homs for arbitrary original object types. -/
theorem fixedObject_geometric_weak_equivalence_iff_factors {O : Type u}
    {G H : FixedDaggerSimplicialGraph O} (f : G ⟶ H) :
    (∀ x y : O, SSet.KanComplex.W (TopCat.toSSet.map (SSet.toTop.map (f.map x y)))) ↔
      (∀ p : ChosenUpper O, SSet.KanComplex.W (TopCat.toSSet.map
        (SSet.toTop.map (((fixedObjectDecomposition O).functor.map f).1 p)))) ∧
      (∀ x : O, SSet.KanComplex.W (TopCat.toSSet.map
        (SSet.toTop.map ((((fixedObjectDecomposition O).functor.map f).2 x).app PUnit.unit)))) :=
  @geometric_weak_equivalence_iff_factors.{u} O (chosenLinearOrder O) G H f

end DaggerFixedGraph
