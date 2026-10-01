import DaggerModels.SSetBoundaryCells
import DaggerModels.SSetMonoRLPRetraction

/-! The actual ordinary boundary-RLP condition supplies a section and a
simplicial cylinder homotopy over the target. This does not yet identify a
weak-equivalence predicate or a model structure. -/

open CategoryTheory MonoidalCategory Simplicial

universe u

namespace DaggerModels.SSetMonoRLPRetraction

theorem exists_section_homotopy_of_boundary_rlp {X Y : SSet.{u}} (p : X ⟶ Y)
    (hp : SSet.modelCategoryQuillen.I.{u}.rlp p) :
    ∃ (s : Y ⟶ X) (H : X ⊗ Δ[1] ⟶ X),
      s ≫ p = 𝟙 Y ∧ SSet.ι₀ ≫ H = p ≫ s ∧ SSet.ι₁ ≫ H = 𝟙 X ∧
        H ≫ p = CartesianMonoidalCategory.fst X Δ[1] ≫ p := by
  apply exists_section_homotopy p
  simpa only [SSetBoundaryCells.I_rlp_eq_monomorphisms_rlp] using hp

end DaggerModels.SSetMonoRLPRetraction
