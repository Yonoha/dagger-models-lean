import DaggerModels
import TopCatModelCategory.ModelCategorySSet

/-! Private integration of the checked ordinary Kan–Quillen comparison with
Part I `bg.lem.I-inj`. The generator family, all hom spaces, and the geometric
weak-equivalence structure are the existing ones. No source/target fibrancy
or dagger model structure is assumed. This file does not change public pins. -/

open CategoryTheory HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

universe u

namespace DaggerModels.KanQuillenReuse

/-- The existing boundary family includes all dimensions, including zero. -/
theorem boundary_lifting_iff_rlp {X Y : SSet.{u}} (p : X ⟶ Y) :
    (∀ n : ℕ, HasLiftingProperty (SSet.boundary.{u} n).ι p) ↔
      SSet.modelCategoryQuillen.I.rlp p := by
  constructor
  · intro h
    rintro A B f ⟨n⟩
    exact h n
  · intro h n
    exact h _ (SSet.modelCategoryQuillen.boundary_ι_mem_I n)

/-- Ordinary boundary lifting is exactly a Kan fibration and a geometric weak equivalence. -/
theorem boundary_lifting_iff_trivial {X Y : SSet.{u}} (p : X ⟶ Y) :
    (∀ n : ℕ, HasLiftingProperty (SSet.boundary.{u} n).ι p) ↔
      Fibration p ∧ WeakEquivalence p := by
  rw [boundary_lifting_iff_rlp, SSet.modelCategoryQuillen.rlp_I_eq_trivialFibrations,
    mem_trivialFibrations_iff]

/-- The weak-equivalence meaning is realization followed by the singular Kan complex. -/
theorem weakEquivalence_iff_geometric {X Y : SSet.{u}} (p : X ⟶ Y) :
    WeakEquivalence p ↔
      SSet.KanComplex.W (TopCat.toSSet.map (SSet.toTop.map p)) := by
  rw [SSet.modelCategoryQuillen.weakEquivalence_iff,
    TopCat.modelCategory.weakEquivalence_iff]

/-- Part I `bg.lem.I-inj`, for the actual dagger generator family and all hom spaces. -/
theorem generators_rlp_iff_trivial
    {C D : DaggerSimplicialCat.{u, u}} (p : C ⟶ D) :
    DaggerGeneratingCofibrations.generators.rlp p ↔
      Function.Surjective p.obj ∧
        ∀ x y : C.Obj, Fibration (p.map x y) ∧ WeakEquivalence (p.map x y) := by
  rw [DaggerGeneratingCofibrations.generators_rlp_iff]
  constructor
  · rintro ⟨ho, h⟩
    exact ⟨ho, fun x y ↦ (boundary_lifting_iff_trivial (p.map x y)).1 (h x y)⟩
  · rintro ⟨ho, h⟩
    exact ⟨ho, fun x y ↦ (boundary_lifting_iff_trivial (p.map x y)).2 (h x y)⟩

/-- The same manuscript conclusion with the ordinary weak-equivalence definition exposed. -/
theorem generators_rlp_iff_geometric
    {C D : DaggerSimplicialCat.{u, u}} (p : C ⟶ D) :
    DaggerGeneratingCofibrations.generators.rlp p ↔
      Function.Surjective p.obj ∧ ∀ x y : C.Obj,
        Fibration (p.map x y) ∧
          SSet.KanComplex.W (TopCat.toSSet.map (SSet.toTop.map (p.map x y))) := by
  rw [generators_rlp_iff_trivial]
  constructor
  · rintro ⟨ho, h⟩
    exact ⟨ho, fun x y ↦ ⟨(h x y).1,
      (weakEquivalence_iff_geometric (p.map x y)).1 (h x y).2⟩⟩
  · rintro ⟨ho, h⟩
    exact ⟨ho, fun x y ↦ ⟨(h x y).1,
      (weakEquivalence_iff_geometric (p.map x y)).2 (h x y).2⟩⟩

end DaggerModels.KanQuillenReuse
