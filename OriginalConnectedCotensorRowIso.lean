import NativeConnectedIhomFamily
import NativeIhomFinitePi
import NativeIhomBinaryProduct
import NativeFamilyIsomorphisms
import OriginalCotensorPiZeroGroupoid
import OriginalBarRowFullData

/-! Full original base/bar rows commute with the exact original connected cotensor. -/
set_option autoImplicit false
open CategoryTheory Simplicial Opposite MonoidalCategory MonoidalClosed DaggerModels
open DaggerOriginalProductGadget DaggerNativeFamilyIsomorphisms
open DaggerNativeConnectedIhomFamily DaggerNativeIhomFinitePi DaggerNativeIhomBinaryProduct
open DaggerOriginalCotensorPrecompositionWeak DaggerOriginalNerveRowChainData
open DaggerOriginalBarRowFullData DaggerOriginalSimplicialCategoryBarRows
universe u
namespace DaggerOriginalConnectedCotensorRowIso
noncomputable section

def arrowFamilyIhomIso (K : SSet.{u}) (C : SimplicialCat.{u, u}) {k : ℕ}
    (O : Fin (k + 1) → C.Obj) :
    arrowFamily (originalCotensor K C) O ≅ (ihom K).obj (arrowFamily C O) :=
  piIhomIso K (fun i : Fin k ↦ C.enriched.Hom (O i.castSucc) (O i.succ))

def baseRowIhomIso (K : SSet.{u}) [Subsingleton K.π₀] (v : K _⦋0⦌)
    (C : SimplicialCat.{u, u}) (k : ℕ) :
    baseRow (originalCotensor K C) k ≅ (ihom K).obj (baseRow C k) :=
  rowChainIso (originalCotensor K C) k ≪≫
    familyIso (fun O ↦ arrowFamilyIhomIso K C O) ≪≫
    familyIhomIso K v (arrowFamily C) ≪≫
    (ihom K).mapIso (rowChainIso C k).symm

def barFactorIhomIso (K : SSet.{u}) (C : SimplicialCat.{u, u}) (z : C.Obj) {k : ℕ}
    (O : Fin (k + 1) → C.Obj) :
    arrowFamily (originalCotensor K C) O ⊗
        (originalCotensor K C).enriched.Hom (O (Fin.last k)) z ≅
      (ihom K).obj (arrowFamily C O ⊗ C.enriched.Hom (O (Fin.last k)) z) :=
  (tensorRight ((ihom K).obj (C.enriched.Hom (O (Fin.last k)) z))).mapIso
      (arrowFamilyIhomIso K C O) ≪≫
    tensorIhomIso K (arrowFamily C O) (C.enriched.Hom (O (Fin.last k)) z)

def barRowIhomIso (K : SSet.{u}) [Subsingleton K.π₀] (v : K _⦋0⦌)
    (C : SimplicialCat.{u, u}) (z : C.Obj) (k : ℕ) :
    barRow (originalCotensor K C) z k ≅ (ihom K).obj (barRow C z k) :=
  barRowDataIso (originalCotensor K C) z k ≪≫
    familyIso (fun O ↦ barFactorIhomIso K C z O) ≪≫
    familyIhomIso K v (fun O : Fin (k + 1) → C.Obj ↦
      arrowFamily C O ⊗ C.enriched.Hom (O (Fin.last k)) z) ≪≫
    (ihom K).mapIso (barRowDataIso C z k).symm

end
end DaggerOriginalConnectedCotensorRowIso
