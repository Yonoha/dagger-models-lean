import FixedCategorySingleCell
import CoproductCellSerialization
import FixedCategorySmallObject

set_option autoImplicit false

/-! Complete acyclicity of the original fixed-category J left class. -/

open CategoryTheory Limits MorphismProperty DaggerModels
open DaggerFixedCategoryGenerators DaggerFixedCategoryHomTransfinite

universe u

namespace DaggerFixedCategoryCellClosure

variable (O : Type u)

/-- Serialize every original small batch, then apply the existing all-Hom closure. -/
theorem batch_le_Q : (coproducts.{u} (J O)).pushouts ≤ Q O :=
  (DaggerCoproductCellSerialization.coproduct_pushouts_le (J O)).trans
    ((transfiniteCompositions_monotone.{u}
      (DaggerFixedCategorySingleCell.J_pushouts_le_Q O)).trans
        (transfiniteCompositions_le (Q O)))

/-- All original transfinite cell complexes, with no restriction on their index order. -/
theorem cells_le_Q :
    transfiniteCompositions.{u} (coproducts.{u} (J O)).pushouts ≤ Q O :=
  (transfiniteCompositions_monotone.{u} (batch_le_Q O)).trans
    (transfiniteCompositions_le (Q O))

theorem cells_le_W :
    transfiniteCompositions.{u} (coproducts.{u} (J O)).pushouts ≤ W O :=
  (cells_le_Q O).trans (Q_le_W O)

/-- The actual SOA and original W retract closure prove the complete original left class. -/
theorem J_rlp_llp_le_W : (J O).rlp.llp ≤ W O := by
  have : HasSmallObjectArgument.{u} (J O) :=
    DaggerFixedCategorySmallObject.J_hasSmallObjectArgument O
  rw [llp_rlp_of_hasSmallObjectArgument]
  exact (retracts_monotone (cells_le_W O)).trans (retracts_le (W O))

/-- Every original Hom map has exactly the original geometric weak-equivalence meaning. -/
theorem J_rlp_llp_hom_geometric {C D : FixedDaggerSimplicialCat O} (f : C ⟶ D)
    (hf : (J O).rlp.llp f) : ∀ x y : O,
    SSet.KanComplex.W (TopCat.toSSet.map (SSet.toTop.map (f.val.map x y))) :=
  (W_iff_geometric f).1 (J_rlp_llp_le_W O f hf)

end DaggerFixedCategoryCellClosure
