import NativeOverChainFullDataEquivalence
import OriginalNerveRowChainData
import OriginalSSetFamilySigmaReconciledRecovered

/-! Every original bar row is exactly the full original Hom family including its last Hom. -/
set_option autoImplicit false
open CategoryTheory Simplicial Opposite MonoidalCategory DaggerModels
open DaggerNativeOverChainFullDataEquivalence DaggerOriginalNerveRowChainData
open DaggerOriginalProductGadget DaggerOriginalSimplicialDegreeCategory
open DaggerOriginalSimplicialCategoryBarRows
universe u
namespace DaggerOriginalBarRowFullData
noncomputable section

def barRowFamily (C : SimplicialCat.{u, u}) (z : C.Obj) (k : ℕ) : SSet.{u} :=
  familySSet (fun O : Fin (k + 1) → C.Obj ↦
    arrowFamily C O ⊗ C.enriched.Hom (O (Fin.last k)) z)

def barRowDataIso (C : SimplicialCat.{u, u}) (z : C.Obj) (k : ℕ) :
    barRow C z k ≅ barRowFamily C z k :=
  NatIso.ofComponents (fun n ↦ (overChainDataEquiv (degreeObjects C n) z k).toIso) (by
    intro n m α
    funext B
    rfl)

theorem barRowDataIso_hom_apply (C : SimplicialCat.{u, u}) (z : C.Obj) (k : ℕ)
    (n : SimplexCategoryᵒᵖ) (B : (barRow C z k).obj n) :
    (barRowDataIso C z k).hom.app n B =
      ⟨(B ⋙ Over.forget (T := degreeObjects C n) z).obj,
        (fun i ↦ (B ⋙ Over.forget (T := degreeObjects C n) z).map
          (homOfLE (Fin.castSucc_le_succ i)),
          (B.obj (Fin.last k)).hom)⟩ := rfl

end
end DaggerOriginalBarRowFullData
