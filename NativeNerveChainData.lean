import Mathlib.AlgebraicTopology.SimplicialSet.Nerve

/-! Whole native nerve chains are object lists with their successive original arrows. -/
set_option autoImplicit false
open CategoryTheory
universe u v w t
namespace DaggerNativeNerveChainData
noncomputable section

def chainDataEquiv (C : Type u) [Category.{v} C] (k : ℕ) :
    (Fin (k + 1) ⥤ C) ≃
      Σ O : Fin (k + 1) → C, ∀ i : Fin k, O i.castSucc ⟶ O i.succ where
  toFun A := ⟨A.obj, fun i ↦ A.map (homOfLE (Fin.castSucc_le_succ i))⟩
  invFun d := ComposableArrows.mkOfObjOfMapSucc d.1 d.2
  left_inv A := by
    refine ComposableArrows.ext ?_ ?_
    · intro i
      rfl
    · intro i hi
      simp only [ComposableArrows.mkOfObjOfMapSucc_map_succ, eqToHom_refl,
        Category.id_comp, Category.comp_id]
  right_inv d := by
    refine Sigma.ext ?_ ?_
    · rfl
    apply heq_of_eq
    funext i
    exact ComposableArrows.mkOfObjOfMapSucc_map_succ d.1 d.2 i.val i.isLt

theorem chainDataEquiv_objects (C : Type u) [Category.{v} C] (k : ℕ)
    (A : Fin (k + 1) ⥤ C) : (chainDataEquiv C k A).1 = A.obj := rfl

theorem chainDataEquiv_arrows (C : Type u) [Category.{v} C] (k : ℕ)
    (A : Fin (k + 1) ⥤ C) (i : Fin k) :
    (chainDataEquiv C k A).2 i = A.map (homOfLE (Fin.castSucc_le_succ i)) := rfl

theorem chainDataEquiv_post {C : Type u} [Category.{v} C] {D : Type w} [Category.{t} D]
    (F : C ⥤ D) (k : ℕ) (A : Fin (k + 1) ⥤ C) :
    chainDataEquiv D k (A ⋙ F) =
      ⟨fun i ↦ F.obj (A.obj i), fun i ↦ F.map (A.map (homOfLE (Fin.castSucc_le_succ i)))⟩ :=
  rfl

end
end DaggerNativeNerveChainData
