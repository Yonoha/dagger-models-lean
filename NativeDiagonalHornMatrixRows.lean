import NativeDiagonalHornMatrix
import NativePartialFaceUnionContraction
import NativeFamilyWeak

/-! Every actual vertical row of the diagonal-face matrix inclusion is anodyne. -/
set_option autoImplicit false
open CategoryTheory Limits HomotopicalAlgebra Simplicial Opposite
open DaggerNativeBisimplicialBox DaggerNativeDiagonalHornMatrix
open DaggerNativePartialFaceUnionGeometry DaggerNativePartialFaceUnionContraction
open DaggerOriginalProductGadget DaggerNativeFamilyWeak
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerNativeDiagonalHornMatrixRows
noncomputable section

def constantFamilyBoxIso (T : Type u) (A : SSet.{u}) :
    familySSet (fun _ : T ↦ A) ≅ boxRow T A where
  hom := { app := fun _ p ↦ (p.1, p.2), naturality := by intros; rfl }
  inv := { app := fun _ p ↦ ⟨p.1, p.2⟩, naturality := by intros; rfl }
  hom_inv_id := by
    apply NatTrans.ext
    funext v p
    cases p
    rfl
  inv_hom_id := by
    apply NatTrans.ext
    funext v p
    cases p
    rfl

def rowFamilyIso (n : ℕ) (k : Fin (n + 1)) (h : SimplexCategoryᵒᵖ) :
    familySSet (fun a : (SSet.horn.{u} n k : SSet.{u}).obj h ↦
      (faceUnion (missingFaces k h a) : SSet.{u})) ≅ (matrixRow.{u} k h : SSet.{u}) where
  hom :=
    { app := fun _ p ↦ ⟨(p.1, p.2.val), p.2.property⟩
      naturality := by intros; rfl }
  inv :=
    { app := fun _ p ↦ ⟨p.val.1, ⟨p.val.2, p.property⟩⟩
      naturality := by intros; rfl }
  hom_inv_id := by
    apply NatTrans.ext
    funext v p
    rcases p with ⟨a, ⟨b, hb⟩⟩
    rfl
  inv_hom_id := by
    apply NatTrans.ext
    funext v p
    apply Subtype.ext
    rfl

theorem rowFamily_square (n : ℕ) (k : Fin (n + 1)) (h : SimplexCategoryᵒᵖ) :
    (rowFamilyIso.{u} n k h).hom ≫ (matrixRow k h).ι =
      familyMap (fun a : (SSet.horn.{u} n k : SSet.{u}).obj h ↦
        (faceUnion (missingFaces k h a)).ι) ≫
          (constantFamilyBoxIso ((SSet.horn.{u} n k : SSet.{u}).obj h) Δ[n]).hom := by
  apply NatTrans.ext
  rfl

theorem matrix_row_weak (n : ℕ) (k : Fin (n + 1)) (h : SimplexCategoryᵒᵖ) :
    WeakEquivalence (matrixRow.{u} k h).ι := by
  have : WeakEquivalence (familyMap
      (fun a : (SSet.horn.{u} n k : SSet.{u}).obj h ↦
        (faceUnion (missingFaces k h a)).ι)) :=
    familyMap_weak _ (fun a ↦ inclusion_weak (missingFaces k h a) k
      (missingFaces_missing k h a) (missingFaces_nonempty k h a))
  have : WeakEquivalence (familyMap
      (fun a : (SSet.horn.{u} n k : SSet.{u}).obj h ↦
        (faceUnion (missingFaces k h a)).ι) ≫
          (constantFamilyBoxIso ((SSet.horn.{u} n k : SSet.{u}).obj h) Δ[n]).hom) :=
    inferInstance
  exact weakEquivalence_of_precomp_of_fac (rowFamily_square n k h)

theorem matrix_row_trivial_cofibration (n : ℕ) (k : Fin (n + 1))
    (h : SimplexCategoryᵒᵖ) :
    trivialCofibrations SSet.{u} ((matrixInclusion.{u} n k).app h) := by
  change trivialCofibrations SSet.{u} (matrixRow.{u} k h).ι
  have : WeakEquivalence (matrixRow.{u} k h).ι := matrix_row_weak n k h
  exact (mem_trivialCofibrations_iff _).mpr
    ⟨(SSet.modelCategoryQuillen.cofibration_iff _).mpr inferInstance, inferInstance⟩

theorem matrixInclusion_mono (n : ℕ) (k : Fin (n + 1)) :
    Mono (matrixInclusion.{u} n k) := by
  apply (NatTrans.mono_iff_mono_app _).mpr
  intro h
  change Mono (matrixRow.{u} k h).ι
  infer_instance

end
end DaggerNativeDiagonalHornMatrixRows
