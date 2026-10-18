import OriginalOrdinaryHornGenerators
import OriginalOrdinaryCellLifting
import Mathlib.AlgebraicTopology.SimplicialSet.CategoryWithFibrations

/-!
# Original ordinary horn-cell right lifting and local Kan fibrations

The right lifting property against the actual ordinary two-object horn-cell
family is exactly the Kan fibration condition on every original Hom map.
No condition on object maps or on weak equivalences is asserted.
-/

open CategoryTheory MorphismProperty HomotopicalAlgebra SSet.modelCategoryQuillen

universe u

namespace DaggerModels.OriginalOrdinaryLocalFibrations

/-- The original ordinary horn-cell right class is precisely the local Kan
fibration class, including arbitrary and coincident source object pairs. -/
theorem generators_rlp_iff {C D : SimplicialCat.{u, u}} (p : C ⟶ D) :
    OriginalOrdinaryHornGenerators.generators.rlp p ↔
      ∀ x y : C.Obj, HomotopicalAlgebra.Fibration (p.map x y) := by
  constructor
  · intro hp x y
    apply (SSet.modelCategoryQuillen.fibration_iff (p.map x y)).2
    intro _ _ i hi
    rw [SSet.modelCategoryQuillen.J, MorphismProperty.iSup_iff] at hi
    rcases hi with ⟨n, hi⟩
    cases hi with
    | mk j =>
      have hmem : OriginalOrdinaryHornGenerators.generators
          (OriginalOrdinaryHornGenerators.generator ⟨n, j⟩) := by
        change MorphismProperty.ofHoms OriginalOrdinaryHornGenerators.generator
          (OriginalOrdinaryHornGenerators.generator ⟨n, j⟩)
        exact MorphismProperty.ofHoms.mk
          (f := OriginalOrdinaryHornGenerators.generator.{u})
          (⟨n, j⟩ : OriginalOrdinaryHornGenerators.Index)
      have hcell : HasLiftingProperty
          (OriginalOrdinaryHornGenerators.generator ⟨n, j⟩) p :=
        hp _ hmem
      exact (OriginalOrdinaryCellLifting.hasLiftingProperty_iff
        (SSet.horn (n + 1) j).ι p).1 hcell x y
  · intro h _ _ i hi
    change MorphismProperty.ofHoms OriginalOrdinaryHornGenerators.generator i at hi
    cases hi with
    | mk a =>
      exact (OriginalOrdinaryCellLifting.hasLiftingProperty_iff
        (SSet.horn (a.1 + 1) a.2).ι p).2
          (fun x y ↦ (SSet.modelCategoryQuillen.fibration_iff (p.map x y)).1
            (h x y) _ (SSet.modelCategoryQuillen.horn_ι_mem_J a.1 a.2))

end DaggerModels.OriginalOrdinaryLocalFibrations
