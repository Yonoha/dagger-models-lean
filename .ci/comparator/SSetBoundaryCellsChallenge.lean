import Mathlib.AlgebraicTopology.RelativeCellComplex.Basic
import Mathlib.AlgebraicTopology.SimplicialSet.CategoryWithFibrations
import Mathlib.AlgebraicTopology.SimplicialSet.Monomorphisms

/-! Ordinary boundary-cell inputs toward Part I `bg.lem.I-inj`.
These statements use the actual Mathlib cells, monomorphisms and right lifting
properties. They do not assert weak equivalences or a model structure. -/
set_option warningAsError false

open CategoryTheory HomotopicalAlgebra MorphismProperty

universe u

namespace DaggerModels.SSetBoundaryCells

theorem exists_relativeCellComplex {X Y : SSet.{u}} (i : X ⟶ Y) [Mono i] :
    Nonempty (RelativeCellComplex.{u}
      (fun (_ : ℕ) ↦ fun n : ℕ ↦ (SSet.boundary.{u} n).ι) i) := by sorry

theorem boundaryCells_eq_monomorphisms :
    transfiniteCompositions.{u} (coproducts.{u} SSet.modelCategoryQuillen.I).pushouts =
      monomorphisms SSet.{u} := by sorry

theorem I_rlp_eq_monomorphisms_rlp :
    SSet.modelCategoryQuillen.I.{u}.rlp = (monomorphisms SSet.{u}).rlp := by sorry

end DaggerModels.SSetBoundaryCells
