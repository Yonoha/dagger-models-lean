import NativeReedySmallObject
import NativeBoxUnionRelativeLifting
import NativeReedyBoxUnionLifting

/-! The actual small generating boxes detect exactly the original Reedy matching fibrations. -/
set_option autoImplicit false
open CategoryTheory MorphismProperty HomotopicalAlgebra Simplicial Opposite
open DaggerNativeBisimplicialHorizontalMapping DaggerNativeReedySmallObject
open DaggerNativeBoxUnionRelativeLifting DaggerNativeReedyBoxUnionLifting
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerNativeReedyGeneratingLifting
noncomputable section

theorem horn_trivial (n : ℕ) (k : Fin (n + 2)) :
    trivialCofibrations SSet.{u} (SSet.horn.{u} (n + 1) k).ι := by
  rw [← fibrations_llp]
  intro A B p hp
  have hf : Fibration (C := SSet.{u}) p := (fibration_iff _).mpr hp
  apply (SSet.modelCategoryQuillen.fibration_iff p).mp hf
  simp only [SSet.modelCategoryQuillen.J, MorphismProperty.iSup_iff]
  exact ⟨n, ⟨k⟩⟩

theorem rlp_implies_reedy {X Y : BiSSet.{u}} (f : X ⟶ Y) (hf : J.rlp f) :
    ReedyFibration f := by
  intro m
  apply (SSet.modelCategoryQuillen.fibration_iff _).mpr
  intro A B i hi
  simp only [SSet.modelCategoryQuillen.J, MorphismProperty.iSup_iff] at hi
  obtain ⟨n, ⟨k⟩⟩ := hi
  exact relative_lifting_of_union (SSet.boundary m) (SSet.horn (n + 1) k) f
    (hf _ (generator_mem m n k))

theorem reedy_implies_rlp {X Y : BiSSet.{u}} (f : X ⟶ Y) (hf : ReedyFibration f) :
    J.rlp f := by
  rintro A B i ⟨⟨m, n, k⟩⟩
  have : WeakEquivalence (SSet.horn.{u} (n + 1) k).ι :=
    ((mem_trivialCofibrations_iff _).mp (horn_trivial n k)).2
  exact union_lifting (SSet.boundary m) (SSet.horn (n + 1) k) f hf

theorem rlp_iff_reedy {X Y : BiSSet.{u}} (f : X ⟶ Y) : J.rlp f ↔ ReedyFibration f :=
  ⟨rlp_implies_reedy f, reedy_implies_rlp f⟩

end
end DaggerNativeReedyGeneratingLifting
