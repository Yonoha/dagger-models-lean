import OriginalNerveRowChainData
import NativeFinitePiWeak
import NativeFamilyWeak
import OriginalDiagonalGeometricReconciledRecovered

/-! Original enriched local weak maps with bijective objects preserve the whole diagonal nerve. -/
set_option autoImplicit false
open CategoryTheory Limits HomotopicalAlgebra Opposite Simplicial DaggerModels
open DaggerOriginalNerveRowChainData DaggerNativeFinitePiWeak DaggerNativeFamilyWeak
open DaggerOriginalProductGadget DaggerSSetGluing
open DaggerOriginalSimplicialCategoryBarRows DaggerOriginalSimplicialCategoryDiagonalNerve
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerOriginalNerveLocalWeakPreservation
noncomputable section

def arrowFamilyMap {C D : SimplicialCat.{u, u}} (F : C ⟶ D) {k : ℕ}
    (O : Fin (k + 1) → C.Obj) : arrowFamily C O ⟶ arrowFamily D (fun i ↦ F.obj (O i)) :=
  piMap (fun i ↦ F.map (O i.castSucc) (O i.succ))

theorem arrowFamilyMap_weak {C D : SimplicialCat.{u, u}} (F : C ⟶ D)
    (hF : ∀ x y : C.Obj, WeakEquivalence (F.map x y)) {k : ℕ}
    (O : Fin (k + 1) → C.Obj) : WeakEquivalence (arrowFamilyMap F O) :=
  piMap_weak _ (fun i ↦ hF (O i.castSucc) (O i.succ))

def objectListEquiv {C D : SimplicialCat.{u, u}} (F : C ⟶ D)
    (hO : Function.Bijective F.obj) (k : ℕ) :
    (Fin (k + 1) → C.Obj) ≃ (Fin (k + 1) → D.Obj) :=
  Equiv.piCongrRight (fun _ ↦ Equiv.ofBijective F.obj hO)

def reindexIso {C D : SimplicialCat.{u, u}} (F : C ⟶ D)
    (hO : Function.Bijective F.obj) (k : ℕ) :
    familySSet (fun O : Fin (k + 1) → C.Obj ↦ arrowFamily D (fun i ↦ F.obj (O i))) ≅
      chainRows D k :=
  NatIso.ofComponents (fun n ↦
    (Equiv.sigmaCongrLeft (β := fun O ↦ (arrowFamily D O).obj n)
      (objectListEquiv F hO k)).toIso) (by intro n m α; funext a; rfl)

theorem chainRowsMap_factor {C D : SimplicialCat.{u, u}} (F : C ⟶ D)
    (hO : Function.Bijective F.obj) (k : ℕ) :
    chainRowsMap F k = familyMap (fun O ↦ arrowFamilyMap F O) ≫ (reindexIso F hO k).hom := by
  apply NatTrans.ext
  rfl

theorem chainRowsMap_weak {C D : SimplicialCat.{u, u}} (F : C ⟶ D)
    (hO : Function.Bijective F.obj)
    (hF : ∀ x y : C.Obj, WeakEquivalence (F.map x y)) (k : ℕ) :
    WeakEquivalence (chainRowsMap F k) := by
  have : WeakEquivalence (familyMap (fun O : Fin (k + 1) → C.Obj ↦ arrowFamilyMap F O)) :=
    familyMap_weak _ (fun O ↦ arrowFamilyMap_weak F hF O)
  rw [chainRowsMap_factor F hO k]
  infer_instance

theorem baseRowsMap_weak {C D : SimplicialCat.{u, u}} (F : C ⟶ D)
    (hO : Function.Bijective F.obj)
    (hF : ∀ x y : C.Obj, WeakEquivalence (F.map x y)) (k : ℕ) :
    WeakEquivalence ((baseRowsMap F).app (op ⦋k⦌)) := by
  have : WeakEquivalence (chainRowsMap F k) := chainRowsMap_weak F hO hF k
  have : WeakEquivalence ((rowChainIso C k).hom ≫ chainRowsMap F k) := inferInstance
  exact weakEquivalence_of_postcomp_of_fac (rowChainIso_natural F k)

theorem diagonalNerveMap_weak {C D : SimplicialCat.{u, u}} (F : C ⟶ D)
    (hO : Function.Bijective F.obj)
    (hF : ∀ x y : C.Obj, WeakEquivalence (F.map x y)) :
    WeakEquivalence (diagonalNerveFunctor.map F) := by
  apply (weakEquivalence_iff_GW _).mpr
  apply DaggerOriginalDiagonalGeometric.diagMap_geometric_column
  intro q
  induction q using Opposite.rec with
  | _ q =>
    induction q using SimplexCategory.rec with
    | _ k => exact (weakEquivalence_iff_GW _).mp (baseRowsMap_weak F hO hF k)

end
end DaggerOriginalNerveLocalWeakPreservation
