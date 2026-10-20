import OriginalBarRowFullData
import OriginalNerveRowsPiZero

/-! Original bar pi0 rows are the native over-category nerve of the actual component category. -/
set_option autoImplicit false
open CategoryTheory Simplicial Opposite MonoidalCategory DaggerModels
open DaggerNativeOverChainFullDataEquivalence DaggerOriginalBarRowFullData
open DaggerNativePiZeroProductEquivalence DaggerNativePiZeroFamilyEquivalence
open DaggerOriginalNerveRowChainData DaggerOriginalNerveRowsPiZero
open DaggerOriginalSimplicialCategoryBarRows DaggerOriginalSimplicialPiZeroCategory
open DaggerOriginalSimplicialDegreeCategory
universe u
namespace DaggerOriginalBarRowsPiZero
noncomputable section

def barRowComponentsEquiv (C : SimplicialCat.{u, u}) (z : C.Obj) (k : ℕ) :
    (barRow C z k).π₀ ≃ (nerve (Over (T := componentObjects C) z)) _⦋k⦌ :=
  ((SSet.π₀Functor.mapIso (barRowDataIso C z k)).toEquiv.trans
    (familyComponentsEquiv _ (fun O : Fin (k + 1) → C.Obj ↦
      arrowFamily C O ⊗ C.enriched.Hom (O (Fin.last k)) z))).trans
    ((Equiv.sigmaCongrRight (fun O : Fin (k + 1) → C.Obj ↦
      (productComponentsEquiv (arrowFamily C O) (C.enriched.Hom (O (Fin.last k)) z)).trans
        (Equiv.prodCongr (finitePiComponentsEquiv k
          (fun i ↦ C.enriched.Hom (O i.castSucc) (O i.succ))) (Equiv.refl _)))).trans
            (overChainDataEquiv (componentObjects C) z k).symm)

theorem barRowComponentsEquiv_mk (C : SimplicialCat.{u, u}) (z : C.Obj) (k : ℕ)
    (B : (barRow C z k) _⦋0⦌) :
    barRowComponentsEquiv C z k (SSet.π₀.mk B) = B ⋙ Over.post (vertexFunctor C) := by
  change (overChainDataEquiv (componentObjects C) z k).symm
    ⟨(B ⋙ Over.forget (T := degreeObjects C (op ⦋0⦌)) z).obj,
      (finitePiComponentsEquiv k
        (fun i ↦ C.enriched.Hom
          ((B ⋙ Over.forget (T := degreeObjects C (op ⦋0⦌)) z).obj i.castSucc)
          ((B ⋙ Over.forget (T := degreeObjects C (op ⦋0⦌)) z).obj i.succ))
        (SSet.π₀.mk (fun i ↦ (B ⋙ Over.forget (T := degreeObjects C (op ⦋0⦌)) z).map
          (homOfLE (Fin.castSucc_le_succ i)))), SSet.π₀.mk (B.obj (Fin.last k)).hom)⟩ = _
  rw [finitePiComponentsEquiv_mk]
  apply (overChainDataEquiv (componentObjects C) z k).symm_apply_eq.mpr
  rfl

def barComponentRows (C : SimplicialCat.{u, u}) (z : C.Obj) : SSet.{u} :=
  barRows C z ⋙ SSet.π₀Functor

def barComponentRowsIso (C : SimplicialCat.{u, u}) (z : C.Obj) :
    barComponentRows C z ≅ nerve (Over (T := componentObjects C) z) :=
  NatIso.ofComponents (fun n ↦ (barRowComponentsEquiv C z n.unop.len).toIso) (by
    intro n m α
    funext q
    obtain ⟨B, rfl⟩ := SSet.π₀.mk_surjective q
    change barRowComponentsEquiv C z m.unop.len
      (SSet.mapπ₀ ((barRows C z).map α) (SSet.π₀.mk B)) =
        (nerve (Over (T := componentObjects C) z)).map α
          (barRowComponentsEquiv C z n.unop.len (SSet.π₀.mk B))
    rw [SSet.mapπ₀_mk, barRowComponentsEquiv_mk, barRowComponentsEquiv_mk]
    rfl)

def componentRowProjection (C : SimplicialCat.{u, u}) (z : C.Obj) :
    barComponentRows C z ⟶ componentRows C where
  app n := SSet.mapπ₀ (rowProjection C z n.unop.len)
  naturality n m α := by
    funext q
    obtain ⟨B, rfl⟩ := SSet.π₀.mk_surjective q
    rfl

theorem componentRowsIso_projection (C : SimplicialCat.{u, u}) (z : C.Obj) :
    componentRowProjection C z ≫ (componentRowsIso C).hom =
      (barComponentRowsIso C z).hom ≫
        nerveMap (Over.forget (T := componentObjects C) z) := by
  apply NatTrans.ext
  funext n q
  obtain ⟨B, rfl⟩ := SSet.π₀.mk_surjective q
  change rowComponentsEquiv C n.unop.len
    (SSet.mapπ₀ (rowProjection C z n.unop.len) (SSet.π₀.mk B)) =
      (nerveMap (Over.forget (T := componentObjects C) z)).app n
        (barRowComponentsEquiv C z n.unop.len (SSet.π₀.mk B))
  rw [SSet.mapπ₀_mk, rowComponentsEquiv_mk, barRowComponentsEquiv_mk]
  rfl

end
end DaggerOriginalBarRowsPiZero
