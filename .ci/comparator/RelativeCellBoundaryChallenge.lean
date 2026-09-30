import Mathlib.AlgebraicTopology.SimplicialSet.Boundary
import Mathlib.AlgebraicTopology.SimplicialSet.Skeleton

/-! Part I `dj.lem.free-cof`: ordinary boundary preimages and exact relative-cell normal forms. -/
set_option warningAsError false
open CategoryTheory Simplicial Opposite
universe u
namespace DaggerModels.RelativeCellBoundary

theorem mem_of_epi_pullback_iff {B : SSet.{u}} (K : B.Subcomplex)
    {k n : SimplexCategory} (α : k ⟶ n) [Epi α] (x : B.obj (op n)) :
    B.map α.op x ∈ K.obj (op k) ↔ x ∈ K.obj (op n) := by sorry
theorem characteristic_preimage_relativeSkeleton {A B : SSet.{u}} (i : A ⟶ B) [Mono i]
    (n : ℕ) (σ : B.nonDegenerate n)
    (hσ : σ.1 ∉ Set.range (i.app (op ⦋n⦌))) :
    (SSet.skeletonOfMono i n).preimage (SSet.yonedaEquiv.symm σ.1) = SSet.boundary n := by sorry
theorem relative_stage_complement_iff {A B : SSet.{u}} (i : A ⟶ B) [Mono i]
    {k n : ℕ} (x : B _⦋k⦌) :
    (x ∈ (SSet.skeletonOfMono i (n + 1)).obj (op ⦋k⦌) ∧
      x ∉ (SSet.skeletonOfMono i n).obj (op ⦋k⦌)) ↔
    ∃ (σ : B.nonDegenerate n), σ.1 ∉ Set.range (i.app (op ⦋n⦌)) ∧
      ∃ (α : ⦋k⦌ ⟶ ⦋n⦌), Epi α ∧ x = B.map α.op σ.1 := by sorry
theorem relative_stage_normal_form_unique {B : SSet.{u}} {k n : ℕ}
    (x : B _⦋k⦌) (σ τ : B.nonDegenerate n)
    (α β : ⦋k⦌ ⟶ ⦋n⦌) [Epi α] [Epi β]
    (hα : x = B.map α.op σ.1) (hβ : x = B.map β.op τ.1) :
    σ = τ ∧ α = β := by sorry

end DaggerModels.RelativeCellBoundary
