import DaggerModels.DaggerGeneratingCofibrations
import DaggerModels.SSetBoundaryFibration

/-! The actual local horn generators in Part I `bg.def.IJ`.
Their right lifting property is precisely the ordinary Kan fibration property
on every full hom space. This proves the local part of the fibration condition;
unitary interval lifting and weak equivalences are not asserted here. -/

open CategoryTheory

universe u

namespace DaggerModels.DaggerLocalFibrations

/-- The free two-object horn maps, in all positive dimensions. -/
def localGenerators : MorphismProperty DaggerSimplicialCat.{u, u} :=
  ⨆ n : ℕ, .ofHoms (fun i : Fin (n + 2) ↦
    TwoObjectDaggerCell.functor.map (SSet.horn.{u} (n + 1) i).ι)

variable {C D : DaggerSimplicialCat.{u, u}} (p : C ⟶ D)

open SSet.modelCategoryQuillen

/-- Local horn-cell lifting is exactly the existing Kan fibration condition on homs. -/
theorem local_generators_rlp_iff : localGenerators.rlp p ↔
    ∀ x y : C.Obj, HomotopicalAlgebra.Fibration (p.map x y) := by
  constructor
  · intro hp x y
    rw [SSet.modelCategoryQuillen.fibration_iff]
    intro A B f hf
    simp only [SSet.modelCategoryQuillen.J, MorphismProperty.iSup_iff] at hf
    obtain ⟨n, ⟨i⟩⟩ := hf
    apply (TwoObjectCellLifting.hasLiftingProperty_iff _ p).1 _ x y
    apply hp
    simp only [localGenerators, MorphismProperty.iSup_iff]
    exact ⟨n, .mk i⟩
  · intro hp A B f hf
    simp only [localGenerators, MorphismProperty.iSup_iff] at hf
    obtain ⟨n, ⟨i⟩⟩ := hf
    apply (TwoObjectCellLifting.hasLiftingProperty_iff _ p).2
    intro x y
    have h := hp x y
    rw [SSet.modelCategoryQuillen.fibration_iff] at h
    apply h
    simp only [SSet.modelCategoryQuillen.J, MorphismProperty.iSup_iff]
    exact ⟨n, .mk i⟩

/-- The actual I† lifting condition implies object surjectivity and local Kan fibrations. -/
theorem object_surjective_and_local_fibrations
    (hp : DaggerGeneratingCofibrations.generators.rlp p) :
    Function.Surjective p.obj ∧
      ∀ x y : C.Obj, HomotopicalAlgebra.Fibration (p.map x y) := by
  obtain ⟨ho, hb⟩ := (DaggerGeneratingCofibrations.generators_rlp_iff p).1 hp
  exact ⟨ho, fun x y ↦ SSetBoundaryFibration.fibration_of_boundary_rlp _ (hb x y)⟩

/-- All local horn generators lift against every actual I†-injective morphism. -/
theorem boundary_generators_rlp_le_local_generators_rlp :
    DaggerGeneratingCofibrations.generators.rlp ≤ localGenerators.rlp := by
  intro C D p hp
  exact (local_generators_rlp_iff p).2
    (object_surjective_and_local_fibrations p hp).2

end DaggerModels.DaggerLocalFibrations
