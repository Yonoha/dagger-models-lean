import OriginalBarRowFullData
import NativeSimplexPullbackFibrationDetection
import NativeCoproductMapFibration
import NativeFamilyWeak

/-! Original endpoint row projections are fibrations whenever the original Homs are Kan. -/
set_option autoImplicit false
open CategoryTheory Limits HomotopicalAlgebra Simplicial Opposite MonoidalCategory
open CartesianMonoidalCategory DaggerModels
open DaggerOriginalBarRowFullData DaggerOriginalNerveRowChainData
open DaggerOriginalSimplicialCategoryBarRows DaggerOriginalProductGadget
open DaggerNativeFamilyWeak DaggerNativeCoproductMapFibration
open DaggerNativeSimplexPullbackFibrationDetection
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerOriginalBarRowsProjectionFibration
noncomputable section

def rowFamilyProjection (C : SimplicialCat.{u, u}) (z : C.Obj) (k : ℕ) :
    barRowFamily C z k ⟶ chainRows C k :=
  familyMap (fun O ↦ fst (arrowFamily C O) (C.enriched.Hom (O (Fin.last k)) z))

theorem rowFamilyProjection_square (C : SimplicialCat.{u, u}) (z : C.Obj) (k : ℕ) :
    (barRowDataIso C z k).hom ≫ rowFamilyProjection C z k =
      rowProjection C z k ≫ (rowChainIso C k).hom := by
  apply NatTrans.ext
  rfl

theorem rowFamilyProjection_fibration (C : SimplicialCat.{u, u})
    [∀ x y : C.Obj, IsFibrant (C.enriched.Hom x y)] (z : C.Obj) (k : ℕ) :
    Fibration (rowFamilyProjection C z k) := by
  let A := fun O : Fin (k + 1) → C.Obj ↦
    arrowFamily C O ⊗ C.enriched.Hom (O (Fin.last k)) z
  let B := fun O : Fin (k + 1) → C.Obj ↦ arrowFamily C O
  let f : ∀ O, A O ⟶ B O := fun O ↦ fst _ _
  have : ∀ O, Fibration (f O) := fun O ↦ product_projection_fibration _ _
  have hp : Fibration (Limits.Sigma.map f) := sigma_map_fibration f
  let e : Arrow.mk (Limits.Sigma.map f) ≅ Arrow.mk (rowFamilyProjection C z k) :=
    Arrow.isoMk (familySigmaIso A) (familySigmaIso B)
      (familyMap_coproduct_square f)
  exact (fibration_iff _).mpr
    (((fibrations SSet.{u}).arrow_mk_iso_iff e).mp ((fibration_iff _).mp hp))

theorem endpoint_row_projection_fibration (C : SimplicialCat.{u, u})
    [∀ x y : C.Obj, IsFibrant (C.enriched.Hom x y)] (z : C.Obj) (k : ℕ) :
    Fibration (rowProjection C z k) := by
  have hp := rowFamilyProjection_fibration C z k
  let e : Arrow.mk (rowProjection C z k) ≅ Arrow.mk (rowFamilyProjection C z k) :=
    Arrow.isoMk (barRowDataIso C z k) (rowChainIso C k)
      (rowFamilyProjection_square C z k)
  exact (fibration_iff _).mpr
    (((fibrations SSet.{u}).arrow_mk_iso_iff e).mpr ((fibration_iff _).mp hp))

end
end DaggerOriginalBarRowsProjectionFibration
