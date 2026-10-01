import Mathlib.AlgebraicTopology.SimplicialSet.CategoryWithFibrations
import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal

/-! Ordinary lifting inputs toward Part I `bg.lem.I-inj`.
The same section and cylinder homotopy must satisfy all four displayed laws.
No weak-equivalence or model-category structure is assumed or concluded. -/
set_option warningAsError false

open CategoryTheory MonoidalCategory Simplicial MorphismProperty

universe u

namespace DaggerModels.SSetMonoRLPRetraction

theorem exists_section_homotopy {X Y : SSet.{u}} (p : X ⟶ Y)
    (hp : (monomorphisms SSet.{u}).rlp p) :
    ∃ (s : Y ⟶ X) (H : X ⊗ Δ[1] ⟶ X),
      s ≫ p = 𝟙 Y ∧ SSet.ι₀ ≫ H = p ≫ s ∧ SSet.ι₁ ≫ H = 𝟙 X ∧
        H ≫ p = CartesianMonoidalCategory.fst X Δ[1] ≫ p := by sorry

theorem exists_section_homotopy_of_boundary_rlp {X Y : SSet.{u}} (p : X ⟶ Y)
    (hp : SSet.modelCategoryQuillen.I.{u}.rlp p) :
    ∃ (s : Y ⟶ X) (H : X ⊗ Δ[1] ⟶ X),
      s ≫ p = 𝟙 Y ∧ SSet.ι₀ ≫ H = p ≫ s ∧ SSet.ι₁ ≫ H = 𝟙 X ∧
        H ≫ p = CartesianMonoidalCategory.fst X Δ[1] ≫ p := by sorry

end DaggerModels.SSetMonoRLPRetraction
