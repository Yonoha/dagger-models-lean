import NativeNerveChainData
import OriginalSimplicialCategoryBarRows

/-! Every original enriched nerve row is the full object-list and original Hom-arrow family. -/
set_option autoImplicit false
open CategoryTheory Opposite Simplicial DaggerModels
open DaggerNativeNerveChainData DaggerOriginalSimplicialDegreeCategory
open DaggerOriginalSimplicialCategoryBarRows DaggerOriginalSimplicialCategoryDiagonalNerve
universe u
namespace DaggerOriginalNerveRowChainData
noncomputable section

def arrowFamily (C : SimplicialCat.{u, u}) {k : ℕ} (O : Fin (k + 1) → C.Obj) : SSet.{u} where
  obj n := ∀ i : Fin k, (C.enriched.Hom (O i.castSucc) (O i.succ)).obj n
  map α a i := (C.enriched.Hom (O i.castSucc) (O i.succ)).map α (a i)
  map_id n := by
    funext a i
    exact congrFun ((C.enriched.Hom (O i.castSucc) (O i.succ)).map_id n) (a i)
  map_comp α β := by
    funext a i
    exact congrFun ((C.enriched.Hom (O i.castSucc) (O i.succ)).map_comp α β) (a i)

def chainRows (C : SimplicialCat.{u, u}) (k : ℕ) : SSet.{u} where
  obj n := Σ O : Fin (k + 1) → C.Obj, (arrowFamily C O).obj n
  map α a := ⟨a.1, (arrowFamily C a.1).map α a.2⟩
  map_id n := by
    funext a
    refine Sigma.ext rfl ?_
    exact heq_of_eq (congrFun ((arrowFamily C a.1).map_id n) a.2)
  map_comp α β := by
    funext a
    refine Sigma.ext rfl ?_
    exact heq_of_eq (congrFun ((arrowFamily C a.1).map_comp α β) a.2)

def rowChainIso (C : SimplicialCat.{u, u}) (k : ℕ) : baseRow C k ≅ chainRows C k :=
  NatIso.ofComponents (fun n ↦ (chainDataEquiv (degreeObjects C n) k).toIso) (by
    intro n m α
    funext A
    rfl)

theorem rowChainIso_hom_objects (C : SimplicialCat.{u, u}) (k : ℕ)
    (n : SimplexCategoryᵒᵖ) (A : (baseRow C k).obj n) :
    ((rowChainIso C k).hom.app n A).1 = A.obj := rfl

theorem rowChainIso_hom_arrows (C : SimplicialCat.{u, u}) (k : ℕ)
    (n : SimplexCategoryᵒᵖ) (A : (baseRow C k).obj n) (i : Fin k) :
    ((rowChainIso C k).hom.app n A).2 i =
      A.map (homOfLE (Fin.castSucc_le_succ i)) := rfl

def chainRowsMap {C D : SimplicialCat.{u, u}} (F : C ⟶ D) (k : ℕ) :
    chainRows C k ⟶ chainRows D k where
  app n a := ⟨fun i ↦ F.obj (a.1 i),
    fun i ↦ (F.map (a.1 i.castSucc) (a.1 i.succ)).app n (a.2 i)⟩
  naturality n m α := by
    funext a
    refine Sigma.ext rfl ?_
    apply heq_of_eq
    funext i
    exact congrFun ((F.map (a.1 i.castSucc) (a.1 i.succ)).naturality α) (a.2 i)

def baseRowsMap {C D : SimplicialCat.{u, u}} (F : C ⟶ D) : baseRows C ⟶ baseRows D :=
  (flipFunctor SimplexCategoryᵒᵖ SimplexCategoryᵒᵖ (Type u)).map
    (bisimplicialNerveFunctor.map F)

theorem rowChainIso_natural {C D : SimplicialCat.{u, u}} (F : C ⟶ D) (k : ℕ) :
    (baseRowsMap F).app (op ⦋k⦌) ≫ (rowChainIso D k).hom =
      (rowChainIso C k).hom ≫ chainRowsMap F k := by
  apply NatTrans.ext
  rfl

end
end DaggerOriginalNerveRowChainData
