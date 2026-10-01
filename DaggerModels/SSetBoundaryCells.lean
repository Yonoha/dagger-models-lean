import DaggerModels.SSetBoundaryCellsAttachment
import Mathlib.AlgebraicTopology.SimplicialSet.CategoryWithFibrations
import Mathlib.AlgebraicTopology.SimplicialSet.Monomorphisms
import Mathlib.CategoryTheory.SmallObject.TransfiniteCompositionLifting

/-!
The independent ordinary relative boundary-cell presentation retains the
original mono and its original source/target. Its lifting conclusion concerns
Mathlib's actual boundary family `SSet.modelCategoryQuillen.I`; it does not
assert weak equivalences, trivial fibrations, or a model category structure.
-/

open CategoryTheory Limits Simplicial HomotopicalAlgebra MorphismProperty

universe u

namespace DaggerModels.SSetBoundaryCells

noncomputable section

/-- Every ordinary simplicial mono is an actual countable relative boundary-cell complex. -/
def relativeCellComplex {X Y : SSet.{u}} (i : X ⟶ Y) [Mono i] :
    RelativeCellComplex.{u} (fun (_ : ℕ) ↦ fun n : ℕ ↦ (SSet.boundary.{u} n).ι) i where
  toTransfiniteCompositionOfShape := transfiniteComposition i
  attachCells n _ := attachCells i n

/-- A relative presentation exists without assuming cellularity or a model structure. -/
theorem exists_relativeCellComplex {X Y : SSet.{u}} (i : X ⟶ Y) [Mono i] :
    Nonempty (RelativeCellComplex.{u}
      (fun (_ : ℕ) ↦ fun n : ℕ ↦ (SSet.boundary.{u} n).ι) i) :=
  ⟨relativeCellComplex i⟩

/-- Reindexing the actual countable presentation keeps the full value universe. -/
theorem mono_mem_boundaryCells {X Y : SSet.{u}} (i : X ⟶ Y) [Mono i] :
    transfiniteCompositions.{u} (coproducts.{u} SSet.modelCategoryQuillen.I).pushouts i := by
  let : SuccOrder (ULift.{u} ℕ) := SuccOrder.ofOrderIso ULift.orderIso.symm
  have h := (relativeCellComplex i).transfiniteCompositionOfShape
    (fun n : ℕ ↦ (SSet.boundary.{u} n).ι)
  have h' := h.ofOrderIso (ULift.orderIso : ULift.{u} ℕ ≃o ℕ)
  rw [transfiniteCompositions_iff]
  exact ⟨ULift.{u} ℕ, inferInstance, inferInstance, inferInstance, inferInstance, ⟨h'⟩⟩

/-- Monomorphisms are precisely the actual transfinite compositions of boundary attachments. -/
theorem boundaryCells_eq_monomorphisms :
    transfiniteCompositions.{u} (coproducts.{u} SSet.modelCategoryQuillen.I).pushouts =
      monomorphisms SSet.{u} := by
  apply le_antisymm
  · rw [transfiniteCompositions_le_iff, pushouts_le_iff, coproducts_le_iff]
    exact SSet.modelCategoryQuillen.I_le_monomorphisms
  · intro X Y i hi
    let : Mono i := hi
    exact mono_mem_boundaryCells i

/-- Lifting against the actual ordinary boundaries is equivalent to lifting against all monos. -/
theorem I_rlp_eq_monomorphisms_rlp :
    SSet.modelCategoryQuillen.I.{u}.rlp = (monomorphisms SSet.{u}).rlp := by
  apply le_antisymm
  · intro X Y p hp A B i hi
    let : Mono i := hi
    exact (transfiniteCompositions_pushouts_coproducts_le_llp_rlp
      SSet.modelCategoryQuillen.I i (mono_mem_boundaryCells i)) p hp
  · exact antitone_rlp SSet.modelCategoryQuillen.I_le_monomorphisms

end
end DaggerModels.SSetBoundaryCells
