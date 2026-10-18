import OriginalNerveLocalWeakPreservation
import OriginalCotensorEvaluationRowMaps

/-! Actual full bar row maps preserve local weak equivalences with bijective objects. -/
set_option autoImplicit false
open CategoryTheory MonoidalCategory Simplicial Opposite HomotopicalAlgebra DaggerModels
open DaggerOriginalNerveRowChainData DaggerOriginalNerveLocalWeakPreservation
open DaggerOriginalBarRowFullData DaggerNativeFamilyWeak DaggerOriginalProductGadget
open DaggerOriginalCotensorEvaluationRowMaps DaggerOriginalSimplicialCategoryBarRows
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerOriginalBarRowsLocalWeakPreservation
noncomputable section

def barArrowFamilyMap {C D : SimplicialCat.{u, u}} (F : C ⟶ D) (z : C.Obj) {k : ℕ}
    (O : Fin (k + 1) → C.Obj) :
    arrowFamily C O ⊗ C.enriched.Hom (O (Fin.last k)) z ⟶
      arrowFamily D (fun i ↦ F.obj (O i)) ⊗
        D.enriched.Hom (F.obj (O (Fin.last k))) (F.obj z) :=
  arrowFamilyMap F O ⊗ₘ F.map (O (Fin.last k)) z

theorem barArrowFamilyMap_weak {C D : SimplicialCat.{u, u}} (F : C ⟶ D)
    (hF : ∀ x y : C.Obj, WeakEquivalence (F.map x y)) (z : C.Obj) {k : ℕ}
    (O : Fin (k + 1) → C.Obj) : WeakEquivalence (barArrowFamilyMap F z O) := by
  apply (DaggerSSetProductGeometric.geometric_iff_weakEquivalence _).mp
  exact DaggerSSetProductGeometric.tensorMap_geometric _ _
    ((DaggerSSetProductGeometric.geometric_iff_weakEquivalence _).mpr
      (arrowFamilyMap_weak F hF O))
    ((DaggerSSetProductGeometric.geometric_iff_weakEquivalence _).mpr
      (hF (O (Fin.last k)) z))

def barReindexIso {C D : SimplicialCat.{u, u}} (F : C ⟶ D)
    (hO : Function.Bijective F.obj) (z : C.Obj) (k : ℕ) :
    familySSet (fun O : Fin (k + 1) → C.Obj ↦
      arrowFamily D (fun i ↦ F.obj (O i)) ⊗
        D.enriched.Hom (F.obj (O (Fin.last k))) (F.obj z)) ≅
      barRowFamily D (F.obj z) k :=
  NatIso.ofComponents (fun n ↦
    (Equiv.sigmaCongrLeft (β := fun O : Fin (k + 1) → D.Obj ↦
      (arrowFamily D O ⊗ D.enriched.Hom (O (Fin.last k)) (F.obj z)).obj n)
      (objectListEquiv F hO k)).toIso) (by intro n m α; funext a; rfl)

theorem barRowDataIso_natural {C D : SimplicialCat.{u, u}} (F : C ⟶ D)
    (hO : Function.Bijective F.obj) (z : C.Obj) (k : ℕ) :
    (barRowsMap F z).app (op ⦋k⦌) ≫ (barRowDataIso D (F.obj z) k).hom =
      (barRowDataIso C z k).hom ≫ familyMap (fun O ↦ barArrowFamilyMap F z O) ≫
        (barReindexIso F hO z k).hom := by
  apply NatTrans.ext
  rfl

theorem barRowsMap_weak {C D : SimplicialCat.{u, u}} (F : C ⟶ D)
    (hO : Function.Bijective F.obj)
    (hF : ∀ x y : C.Obj, WeakEquivalence (F.map x y)) (z : C.Obj) (k : ℕ) :
    WeakEquivalence ((barRowsMap F z).app (op ⦋k⦌)) := by
  have : WeakEquivalence (familyMap
      (fun O : Fin (k + 1) → C.Obj ↦ barArrowFamilyMap F z O)) :=
    familyMap_weak _ (fun O ↦ barArrowFamilyMap_weak F hF z O)
  have : WeakEquivalence ((barRowDataIso C z k).hom ≫
      familyMap (fun O ↦ barArrowFamilyMap F z O) ≫ (barReindexIso F hO z k).hom) :=
    inferInstance
  exact weakEquivalence_of_postcomp_of_fac (barRowDataIso_natural F hO z k)

end
end DaggerOriginalBarRowsLocalWeakPreservation
