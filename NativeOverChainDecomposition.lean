import OriginalOverNerveFibreChallengeProof

/-!
# Native over-category chains are base chains with one final arrow

Reuse Mathlib's Functor.toOver to reconstruct the whole chain from its native
projection and its last arrow. This applies to every base chain, not only a
constant vertex chain. No homotopical assertion is assumed.
-/
set_option autoImplicit false
open CategoryTheory
open DaggerOriginalOverNerveFibreChallengeProof
universe u
namespace DaggerNativeOverChainDecomposition
noncomputable section

/-- Lift the entire original base chain using its original last arrow to the endpoint. -/
def chainLift {T : Type u} [Category.{u} T] {z : T} {n : ℕ}
    (A : Fin (n + 1) ⥤ T) (f : A.obj (Fin.last n) ⟶ z) : Fin (n + 1) ⥤ Over z :=
  A.toOver z (fun k ↦ A.map (homOfLE (Fin.le_last k)) ≫ f) (by
    intro k l e
    rw [← Category.assoc, ← A.map_comp]
    congr 1)

/-- The native lift projects to the exact original chain as an equality of full functors. -/
theorem chainLift_forget {T : Type u} [Category.{u} T] {z : T} {n : ℕ}
    (A : Fin (n + 1) ⥤ T) (f : A.obj (Fin.last n) ⟶ z) :
    chainLift A f ⋙ Over.forget z = A := by
  unfold chainLift
  apply Functor.toOver_comp_forget
  intro k l e
  rw [← Category.assoc, ← A.map_comp]
  congr 1

/-- Each original lifted final arrow is composition along the actual original base chain. -/
theorem chainLift_obj_hom {T : Type u} [Category.{u} T] {z : T} {n : ℕ}
    (A : Fin (n + 1) ⥤ T) (f : A.obj (Fin.last n) ⟶ z) (k : Fin (n + 1)) :
    ((chainLift A f).obj k).hom = A.map (homOfLE (Fin.le_last k)) ≫ f := rfl

/-- The native last arrow of the full lifted chain is precisely the specified final arrow. -/
theorem chainLift_last {T : Type u} [Category.{u} T] {z : T} {n : ℕ}
    (A : Fin (n + 1) ⥤ T) (f : A.obj (Fin.last n) ⟶ z) :
    ((chainLift A f).obj (Fin.last n)).hom = f := by
  rw [chainLift_obj_hom]
  rw [show (homOfLE (Fin.le_last (Fin.last n)) : Fin.last n ⟶ Fin.last n) =
    𝟙 (Fin.last n) from Subsingleton.elim _ _, A.map_id, Category.id_comp]

/-- Recover every original over chain from its entire original projection and last arrow. -/
theorem chain_reconstruct {T : Type u} [Category.{u} T] {z : T} {n : ℕ}
    (B : Fin (n + 1) ⥤ Over z) :
    B = chainLift (B ⋙ Over.forget z) (B.obj (Fin.last n)).hom := by
  have hobj : ∀ k, B.obj k =
      (chainLift (B ⋙ Over.forget z) (B.obj (Fin.last n)).hom).obj k := by
    intro k
    apply overObject_eq (a := B.obj k)
      (b := (chainLift (B ⋙ Over.forget z) (B.obj (Fin.last n)).hom).obj k) rfl
    exact heq_of_eq (Over.w (B.map (homOfLE (Fin.le_last k)))).symm
  refine Functor.hext hobj ?_
  intro k l e
  apply overHom_heq (hobj k) (hobj l)
  rfl

/-- All native over chains biject with the exact base chain and its exact original last arrow. -/
def overChainEquiv (T : Type u) [Category.{u} T] (z : T) (n : ℕ) :
    (Fin (n + 1) ⥤ Over z) ≃
      Σ A : Fin (n + 1) ⥤ T, A.obj (Fin.last n) ⟶ z where
  toFun B := ⟨B ⋙ Over.forget z, (B.obj (Fin.last n)).hom⟩
  invFun p := chainLift p.1 p.2
  left_inv B := (chain_reconstruct B).symm
  right_inv p := by
    rcases p with ⟨A, f⟩
    exact Sigma.ext (chainLift_forget A f) (heq_of_eq (chainLift_last A f))

/-- Every restriction of a chain acts on the final arrow by exact original precomposition. -/
theorem chainLift_precompose {T : Type u} [Category.{u} T] {z : T} {n m : ℕ}
    (A : Fin (n + 1) ⥤ T) (f : A.obj (Fin.last n) ⟶ z)
    (K : Fin (m + 1) ⥤ Fin (n + 1)) :
    K ⋙ chainLift A f = chainLift (K ⋙ A)
      (A.map (homOfLE (Fin.le_last (K.obj (Fin.last m)))) ≫ f) := by
  calc
    K ⋙ chainLift A f = chainLift ((K ⋙ chainLift A f) ⋙ Over.forget z)
        ((K ⋙ chainLift A f).obj (Fin.last m)).hom := chain_reconstruct _
    _ = _ := by
      change (overChainEquiv T z m).symm ⟨_, _⟩ = (overChainEquiv T z m).symm ⟨_, _⟩
      apply congrArg (overChainEquiv T z m).symm
      refine Sigma.ext ?_ HEq.rfl
      change (K ⋙ chainLift A f) ⋙ Over.forget z = K ⋙ A
      rw [Functor.assoc, chainLift_forget]

/-- Every original functor acts on the full lift by its exact original Hom map. -/
theorem chainLift_post {T D : Type u} [Category.{u} T] [Category.{u} D]
    {z : T} {n : ℕ} (A : Fin (n + 1) ⥤ T) (f : A.obj (Fin.last n) ⟶ z)
    (F : T ⥤ D) :
    chainLift A f ⋙ Over.post F = chainLift (A ⋙ F) (F.map f) := by
  have hobj : ∀ k, (chainLift A f ⋙ Over.post F).obj k =
      (chainLift (A ⋙ F) (F.map f)).obj k := by
    intro k
    apply overObject_eq (a := (chainLift A f ⋙ Over.post F).obj k)
      (b := (chainLift (A ⋙ F) (F.map f)).obj k) rfl
    exact heq_of_eq (F.map_comp (A.map (homOfLE (Fin.le_last k))) f)
  refine Functor.hext hobj ?_
  intro k l e
  apply overHom_heq (hobj k) (hobj l)
  rfl

end
end DaggerNativeOverChainDecomposition
