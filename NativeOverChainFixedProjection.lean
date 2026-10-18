import NativeOverChainDecomposition

/-!
# Full native over chains with a prescribed entire projection

Use the already proved native over-chain equivalence. Fixing its first
coordinate leaves exactly the original Hom from the last base object.
-/
set_option autoImplicit false
open CategoryTheory
open DaggerNativeOverChainDecomposition
universe u
namespace DaggerNativeOverChainFixedProjection
noncomputable section

/-- With the entire original base chain fixed, the final arrow determines the full lift. -/
theorem chainLift_injective {T : Type u} [Category.{u} T] {z : T} {k : ℕ}
    (A : Fin (k + 1) ⥤ T) : Function.Injective (chainLift (z := z) A) := by
  intro f g h
  have hp : (⟨A, f⟩ : Σ B : Fin (k + 1) ⥤ T, B.obj (Fin.last k) ⟶ z) = ⟨A, g⟩ :=
    (overChainEquiv T z k).symm.injective h
  exact eq_of_heq (Sigma.mk.inj hp).2

/-- Every full over chain with the specified entire projection is the lift of a final arrow. -/
theorem chainLift_surjective_on_fibre {T : Type u} [Category.{u} T] {z : T} {k : ℕ}
    (A : Fin (k + 1) ⥤ T) (B : Fin (k + 1) ⥤ Over z)
    (h : B ⋙ Over.forget z = A) : ∃ f : A.obj (Fin.last k) ⟶ z, chainLift A f = B := by
  obtain ⟨⟨A', f⟩, hf⟩ := (overChainEquiv T z k).symm.surjective B
  have ha : A' = A := (chainLift_forget A' f).symm.trans
    ((congrArg (fun D ↦ D ⋙ Over.forget z) hf).trans h)
  subst A'
  exact ⟨f, hf⟩

end
end DaggerNativeOverChainFixedProjection
