import NativeFullChainInjectivity

/-! Recover a complete costructured chain from its entire degree chain and final structure map. -/
set_option autoImplicit false
open CategoryTheory
open DaggerNativeFullChainInjectivity
universe u₁ v₁ u₂ v₂
namespace DaggerNativeCostructuredChainDecomposition
noncomputable section

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
variable (S : C ⥤ D)

/-- Lift every original arrow, using the full final structure map. -/
def chainLift {X : D} {n : ℕ} (A : Fin (n + 1) ⥤ C)
    (f : S.obj (A.obj (Fin.last n)) ⟶ X) : Fin (n + 1) ⥤ CostructuredArrow S X where
  obj i := CostructuredArrow.mk (S.map (A.map (homOfLE (Fin.le_last i))) ≫ f)
  map {i j} g := CostructuredArrow.homMk (A.map g) (by
    change S.map (A.map g) ≫ (S.map (A.map (homOfLE (Fin.le_last j))) ≫ f) =
      S.map (A.map (homOfLE (Fin.le_last i))) ≫ f
    rw [← Category.assoc, ← S.map_comp, ← A.map_comp]
    congr 1)
  map_id i := by apply CostructuredArrow.ext; exact A.map_id i
  map_comp g h := by apply CostructuredArrow.ext; exact A.map_comp g h

/-- The exact entire base chain is recovered by the native projection. -/
theorem chainLift_forget {X : D} {n : ℕ} (A : Fin (n + 1) ⥤ C)
    (f : S.obj (A.obj (Fin.last n)) ⟶ X) :
    chainLift S A f ⋙ CostructuredArrow.proj S X = A := rfl

/-- The original last structure map is unchanged. -/
theorem chainLift_last {X : D} {n : ℕ} (A : Fin (n + 1) ⥤ C)
    (f : S.obj (A.obj (Fin.last n)) ⟶ X) :
    ((chainLift S A f).obj (Fin.last n)).hom = f := by
  change S.map (A.map (homOfLE (Fin.le_last (Fin.last n)))) ≫ f = f
  rw [show (homOfLE (Fin.le_last (Fin.last n)) : Fin.last n ⟶ Fin.last n) =
    𝟙 (Fin.last n) from Subsingleton.elim _ _, A.map_id, S.map_id, Category.id_comp]

/-- Full arrow equality is transported along the corresponding full object equalities. -/
theorem hom_heq {X : D} {P Q R T : CostructuredArrow S X}
    (hP : P = R) (hQ : Q = T) (f : P ⟶ Q) (g : R ⟶ T)
    (h : HEq f.left g.left) : HEq f g := by
  cases hP
  cases hQ
  exact heq_of_eq (CostructuredArrow.ext f g (eq_of_heq h))

/-- Reconstruct the whole original functor, retaining every intermediate arrow. -/
theorem chain_reconstruct {X : D} {n : ℕ} (B : Fin (n + 1) ⥤ CostructuredArrow S X) :
    B = chainLift S (B ⋙ CostructuredArrow.proj S X) (B.obj (Fin.last n)).hom := by
  have ho : ∀ i, B.obj i =
      (chainLift S (B ⋙ CostructuredArrow.proj S X) (B.obj (Fin.last n)).hom).obj i := by
    intro i
    apply comma_object_eq (P := B.obj i)
      (Q := (chainLift S (B ⋙ CostructuredArrow.proj S X) (B.obj (Fin.last n)).hom).obj i)
      rfl (Subsingleton.elim _ _)
    exact heq_of_eq (CostructuredArrow.w (B.map (homOfLE (Fin.le_last i)))).symm
  refine CategoryTheory.Functor.hext ho ?_
  intro i j g
  exact hom_heq S (ho i) (ho j) (B.map g) _ HEq.rfl

/-- Complete original chains are equivalent to degree chains with their full last map. -/
def chainEquiv (X : D) (n : ℕ) :
    (Fin (n + 1) ⥤ CostructuredArrow S X) ≃
      Σ A : Fin (n + 1) ⥤ C, S.obj (A.obj (Fin.last n)) ⟶ X where
  toFun B := ⟨B ⋙ CostructuredArrow.proj S X, (B.obj (Fin.last n)).hom⟩
  invFun p := chainLift S p.1 p.2
  left_inv B := (chain_reconstruct S B).symm
  right_inv p := by
    rcases p with ⟨A, f⟩
    exact Sigma.ext (chainLift_forget S A f) (heq_of_eq (chainLift_last S A f))

/-- Every original restriction acts through its actual final chain arrow. -/
theorem chainLift_precompose {X : D} {n m : ℕ} (A : Fin (n + 1) ⥤ C)
    (f : S.obj (A.obj (Fin.last n)) ⟶ X) (K : Fin (m + 1) ⥤ Fin (n + 1)) :
    K ⋙ chainLift S A f = chainLift S (K ⋙ A)
      (S.map (A.map (homOfLE (Fin.le_last (K.obj (Fin.last m))))) ≫ f) := by
  calc
    K ⋙ chainLift S A f = chainLift S ((K ⋙ chainLift S A f) ⋙ CostructuredArrow.proj S X)
        ((K ⋙ chainLift S A f).obj (Fin.last m)).hom := chain_reconstruct S _
    _ = _ := by
      change (chainEquiv S X m).symm ⟨_, _⟩ = (chainEquiv S X m).symm ⟨_, _⟩
      apply congrArg (chainEquiv S X m).symm
      refine Sigma.ext ?_ HEq.rfl
      change (K ⋙ chainLift S A f) ⋙ CostructuredArrow.proj S X = K ⋙ A
      rw [CategoryTheory.Functor.assoc, chainLift_forget]

/-- Every original target map acts by full postcomposition on the final structure map. -/
theorem chainLift_postcompose {X Y : D} {n : ℕ} (A : Fin (n + 1) ⥤ C)
    (f : S.obj (A.obj (Fin.last n)) ⟶ X) (g : X ⟶ Y) :
    chainLift S A f ⋙ CostructuredArrow.map g = chainLift S A (f ≫ g) := by
  have ho : ∀ i, (chainLift S A f ⋙ CostructuredArrow.map g).obj i =
      (chainLift S A (f ≫ g)).obj i := by
    intro i
    apply comma_object_eq (P := (chainLift S A f ⋙ CostructuredArrow.map g).obj i)
      (Q := (chainLift S A (f ≫ g)).obj i) rfl (Subsingleton.elim _ _)
    exact heq_of_eq (Category.assoc _ _ _)
  refine CategoryTheory.Functor.hext ho ?_
  intro i j e
  exact hom_heq S (ho i) (ho j) _ _ HEq.rfl

end
end DaggerNativeCostructuredChainDecomposition
