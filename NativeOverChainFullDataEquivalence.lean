import NativeOverChainDecomposition
import NativeNerveChainData

/-! Entire native over chains retain their original object list, adjacent arrows and last arrow. -/
set_option autoImplicit false
open CategoryTheory
open DaggerNativeOverChainDecomposition DaggerNativeNerveChainData
universe u
namespace DaggerNativeOverChainFullDataEquivalence
noncomputable section

def overChainDataEquiv (T : Type u) [Category.{u} T] (z : T) (k : ℕ) :
    (Fin (k + 1) ⥤ Over z) ≃ Σ O : Fin (k + 1) → T,
      (∀ i : Fin k, O i.castSucc ⟶ O i.succ) × (O (Fin.last k) ⟶ z) :=
  (overChainEquiv T z k).trans
    ((Equiv.sigmaCongr (chainDataEquiv T k) (fun _ ↦ Equiv.refl _)).trans
      ((Equiv.sigmaAssoc (fun (O : Fin (k + 1) → T)
        (_ : ∀ i : Fin k, O i.castSucc ⟶ O i.succ) ↦ O (Fin.last k) ⟶ z)).trans
        (Equiv.sigmaCongrRight (fun O ↦ Equiv.sigmaEquivProd
          (∀ i : Fin k, O i.castSucc ⟶ O i.succ) (O (Fin.last k) ⟶ z)))))

theorem overChainDataEquiv_apply (T : Type u) [Category.{u} T] (z : T) (k : ℕ)
    (B : Fin (k + 1) ⥤ Over z) :
    overChainDataEquiv T z k B =
      ⟨(B ⋙ Over.forget z).obj,
        (fun i ↦ (B ⋙ Over.forget z).map (homOfLE (Fin.castSucc_le_succ i)),
          (B.obj (Fin.last k)).hom)⟩ := rfl

end
end DaggerNativeOverChainFullDataEquivalence
