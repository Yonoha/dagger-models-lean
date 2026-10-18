import NativeBisimplicialBoxUnion
import NativeDiagonalHornMatrixRows

/-! Original box-union row inclusions are anodyne when the original vertical inclusion is. -/
set_option autoImplicit false
open CategoryTheory HomotopicalAlgebra Simplicial Opposite
open DaggerNativeBisimplicialBox DaggerNativeBisimplicialBoxUnion
open DaggerOriginalProductGadget DaggerNativeFamilyWeak
open DaggerNativeDiagonalHornMatrixRows
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerNativeBoxUnionRowsAnodyne
noncomputable section

variable {K B : SSet.{u}} (H : K.Subcomplex) (A : B.Subcomplex)

def piece (h : SimplexCategoryᵒᵖ) (t : K.obj h) : B.Subcomplex where
  obj v b := t ∈ H.obj h ∨ b ∈ A.obj v
  map β _ hb := hb.imp id (fun hb ↦ A.map β hb)

def rowFamilyIso (h : SimplexCategoryᵒᵖ) :
    familySSet (fun t : K.obj h ↦ (piece H A h t : SSet.{u})) ≅
      (unionRow H A h : SSet.{u}) where
  hom :=
    { app := fun _ p ↦ ⟨(p.1, p.2.val), p.2.property⟩
      naturality := by intros; rfl }
  inv :=
    { app := fun _ p ↦ ⟨p.val.1, ⟨p.val.2, p.property⟩⟩
      naturality := by intros; rfl }
  hom_inv_id := by
    apply NatTrans.ext
    funext v p
    rcases p with ⟨t, ⟨b, hb⟩⟩
    rfl
  inv_hom_id := by apply NatTrans.ext; funext v p; apply Subtype.ext; rfl

theorem piece_weak [WeakEquivalence A.ι] (h : SimplexCategoryᵒᵖ) (t : K.obj h) :
    WeakEquivalence (piece H A h t).ι := by
  by_cases ht : t ∈ H.obj h
  · have he : piece H A h t = ⊤ := by
      ext v b
      change (t ∈ H.obj h ∨ b ∈ A.obj v) ↔ True
      exact ⟨fun _ ↦ trivial, fun _ ↦ Or.inl ht⟩
    rw [he]
    change WeakEquivalence (SSet.Subcomplex.topIso B).hom
    infer_instance
  · have he : piece H A h t = A := by
      ext v b
      change (t ∈ H.obj h ∨ b ∈ A.obj v) ↔ b ∈ A.obj v
      exact ⟨fun hb ↦ hb.resolve_left ht, Or.inr⟩
    rw [he]
    infer_instance

theorem rowFamily_square (h : SimplexCategoryᵒᵖ) :
    (rowFamilyIso H A h).hom ≫ (unionRow H A h).ι =
      familyMap (fun t : K.obj h ↦ (piece H A h t).ι) ≫
        (constantFamilyBoxIso (K.obj h) B).hom := by apply NatTrans.ext; rfl

theorem row_weak [WeakEquivalence A.ι] (h : SimplexCategoryᵒᵖ) :
    WeakEquivalence (unionRow H A h).ι := by
  have : WeakEquivalence (familyMap (fun t : K.obj h ↦ (piece H A h t).ι)) :=
    familyMap_weak _ (fun t ↦ piece_weak H A h t)
  have : WeakEquivalence (familyMap (fun t : K.obj h ↦ (piece H A h t).ι) ≫
      (constantFamilyBoxIso (K.obj h) B).hom) := inferInstance
  exact weakEquivalence_of_precomp_of_fac (rowFamily_square H A h)

theorem row_trivial [WeakEquivalence A.ι] (h : SimplexCategoryᵒᵖ) :
    trivialCofibrations SSet.{u} ((unionInclusion H A).app h) := by
  change trivialCofibrations SSet.{u} (unionRow H A h).ι
  have : WeakEquivalence (unionRow H A h).ι := row_weak H A h
  exact (mem_trivialCofibrations_iff _).mpr
    ⟨(SSet.modelCategoryQuillen.cofibration_iff _).mpr inferInstance, inferInstance⟩

end
end DaggerNativeBoxUnionRowsAnodyne
