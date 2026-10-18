import ProofActualSecondConeProjectionWeakness
import NativeOverChainDecomposition

/-! Full chains in the original StructuredArrow category retain their first original arrow. -/
set_option autoImplicit false
open CategoryTheory
universe u
namespace DaggerNativeStructuredArrowChainDecomposition
noncomputable section

variable {C D : Type u} [Category.{u} C] [Category.{u} D] (F : C ⥤ D)

theorem object_eq {s : D} {a b : StructuredArrow s F} (h : a.right = b.right)
    (hh : HEq a.hom b.hom) : a = b := Comma.ext (Subsingleton.elim _ _) h hh

theorem hom_heq {s : D} {a b c d : StructuredArrow s F} (ha : a = c) (hb : b = d)
    (f : a ⟶ b) (g : c ⟶ d) (h : HEq f.right g.right) : HEq f g := by
  cases ha
  cases hb
  exact heq_of_eq (StructuredArrow.hom_ext f g (eq_of_heq h))

/-- Lift the full original base chain by postcomposing its actual first arrow. -/
def chainLift {s : D} {n : ℕ} (c : Fin (n + 1) ⥤ C) (f : s ⟶ F.obj (c.obj 0)) :
    Fin (n + 1) ⥤ StructuredArrow s F where
  obj i := StructuredArrow.mk (Y := c.obj i) (f ≫ F.map (c.map (homOfLE (Fin.zero_le i))))
  map {i j} g := StructuredArrow.homMk (c.map g) (by
    change (f ≫ F.map (c.map _)) ≫ F.map (c.map g) = f ≫ F.map (c.map _)
    rw [Category.assoc, ← F.map_comp, ← c.map_comp]
    congr 2)
  map_id i := by apply StructuredArrow.hom_ext; exact c.map_id i
  map_comp g h := by apply StructuredArrow.hom_ext; exact c.map_comp g h

theorem chainLift_forget {s : D} {n : ℕ} (c : Fin (n + 1) ⥤ C)
    (f : s ⟶ F.obj (c.obj 0)) : chainLift F c f ⋙ StructuredArrow.proj s F = c := rfl

theorem chainLift_first {s : D} {n : ℕ} (c : Fin (n + 1) ⥤ C)
    (f : s ⟶ F.obj (c.obj 0)) : ((chainLift F c f).obj 0).hom = f := by
  change f ≫ F.map (c.map (homOfLE (Fin.zero_le 0))) = f
  rw [show (homOfLE (Fin.zero_le 0) : (0 : Fin (n + 1)) ⟶ 0) = 𝟙 0 from
    Subsingleton.elim _ _, c.map_id, F.map_id, Category.comp_id]

/-- Every actual under-chain is reconstructed as equality of entire functors. -/
theorem chain_reconstruct {s : D} {n : ℕ} (B : Fin (n + 1) ⥤ StructuredArrow s F) :
    chainLift F (B ⋙ StructuredArrow.proj s F) (B.obj 0).hom = B := by
  have hobj : ∀ i,
      (chainLift F (B ⋙ StructuredArrow.proj s F) (B.obj 0).hom).obj i = B.obj i := by
    intro i
    apply object_eq F
      (a := (chainLift F (B ⋙ StructuredArrow.proj s F) (B.obj 0).hom).obj i)
      (b := B.obj i) rfl
    exact heq_of_eq (StructuredArrow.w (B.map (homOfLE (Fin.zero_le i))))
  refine CategoryTheory.Functor.hext hobj ?_
  intro i j f
  apply hom_heq F (hobj i) (hobj j)
  rfl

def chainEquiv (s : D) (n : ℕ) : (Fin (n + 1) ⥤ StructuredArrow s F) ≃
    Σ c : Fin (n + 1) ⥤ C, s ⟶ F.obj (c.obj 0) where
  toFun B := ⟨B ⋙ StructuredArrow.proj s F, (B.obj 0).hom⟩
  invFun p := chainLift F p.1 p.2
  left_inv B := chain_reconstruct F B
  right_inv p := Sigma.ext (chainLift_forget F p.1 p.2) (heq_of_eq (chainLift_first F p.1 p.2))

end
end DaggerNativeStructuredArrowChainDecomposition
