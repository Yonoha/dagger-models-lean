import NativePiZeroProductEquivalence
import NativePiZeroFamilyEquivalence
import OriginalNerveRowChainData
import OriginalSimplicialPiZeroFunctor

/-! The pi0 of every original enriched nerve row is the same full pi0-category nerve. -/
set_option autoImplicit false
open CategoryTheory Opposite Simplicial DaggerModels
open DaggerNativePiZeroProductEquivalence DaggerNativePiZeroFamilyEquivalence
open DaggerNativeFinitePiWeak DaggerNativeNerveChainData
open DaggerOriginalNerveRowChainData DaggerOriginalSimplicialCategoryBarRows
open DaggerOriginalSimplicialPiZeroCategory
open DaggerOriginalSimplicialPiZeroFunctor
universe u
namespace DaggerOriginalNerveRowsPiZero
noncomputable section

def rowComponentsEquiv (C : SimplicialCat.{u, u}) (k : ℕ) :
    (baseRow C k).π₀ ≃ (nerve (componentObjects C)) _⦋k⦌ :=
  ((SSet.π₀Functor.mapIso (rowChainIso C k)).toEquiv.trans
    (familyComponentsEquiv _ (fun O ↦ arrowFamily C O))).trans
    ((Equiv.sigmaCongrRight (fun O : Fin (k + 1) → C.Obj ↦ finitePiComponentsEquiv k
      (fun i ↦ C.enriched.Hom (O i.castSucc) (O i.succ)))).trans
        (chainDataEquiv (componentObjects C) k).symm)

theorem rowComponentsEquiv_mk (C : SimplicialCat.{u, u}) (k : ℕ)
    (A : (baseRow C k) _⦋0⦌) :
    rowComponentsEquiv C k (SSet.π₀.mk A) = A ⋙ vertexFunctor C := by
  change (chainDataEquiv (componentObjects C) k).symm
    ⟨A.obj, finitePiComponentsEquiv k
      (fun i ↦ C.enriched.Hom (A.obj i.castSucc) (A.obj i.succ))
      (SSet.π₀.mk (fun i ↦ A.map (homOfLE (Fin.castSucc_le_succ i))))⟩ = _
  rw [finitePiComponentsEquiv_mk]
  apply (chainDataEquiv (componentObjects C) k).symm_apply_eq.mpr
  rfl

def componentRows (C : SimplicialCat.{u, u}) : SSet.{u} := baseRows C ⋙ SSet.π₀Functor

def componentRowsIso (C : SimplicialCat.{u, u}) :
    componentRows C ≅ nerve (componentObjects C) :=
  NatIso.ofComponents (fun n ↦ (rowComponentsEquiv C n.unop.len).toIso) (by
    intro n m α
    funext q
    obtain ⟨A, rfl⟩ := SSet.π₀.mk_surjective q
    change rowComponentsEquiv C m.unop.len
      (SSet.mapπ₀ ((baseRows C).map α) (SSet.π₀.mk A)) =
        (nerve (componentObjects C)).map α (rowComponentsEquiv C n.unop.len (SSet.π₀.mk A))
    rw [SSet.mapπ₀_mk, rowComponentsEquiv_mk, rowComponentsEquiv_mk]
    rfl)

def componentRowsMap {C D : SimplicialCat.{u, u}} (F : C ⟶ D) :
    componentRows C ⟶ componentRows D :=
  Functor.whiskerRight (baseRowsMap F) SSet.π₀Functor

theorem componentRowsIso_natural {C D : SimplicialCat.{u, u}} (F : C ⟶ D) :
    componentRowsMap F ≫ (componentRowsIso D).hom =
      (componentRowsIso C).hom ≫ nerveMap (componentFunctor F) := by
  apply NatTrans.ext
  funext n q
  obtain ⟨A, rfl⟩ := SSet.π₀.mk_surjective q
  change rowComponentsEquiv D n.unop.len
    (SSet.mapπ₀ ((baseRowsMap F).app n) (SSet.π₀.mk A)) =
      (nerveMap (componentFunctor F)).app n (rowComponentsEquiv C n.unop.len (SSet.π₀.mk A))
  rw [SSet.mapπ₀_mk, rowComponentsEquiv_mk, rowComponentsEquiv_mk]
  change (A ⋙ DaggerOriginalSimplicialDegreeCategory.degreeFunctor F (op ⦋0⦌)) ⋙
      vertexFunctor D = (A ⋙ vertexFunctor C) ⋙ componentFunctor F
  rw [Functor.assoc, vertexFunctor_natural, Functor.assoc]

end
end DaggerOriginalNerveRowsPiZero
