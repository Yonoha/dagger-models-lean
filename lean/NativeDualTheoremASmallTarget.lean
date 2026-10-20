import NativeDualTheoremA

/-! Apply the native dual Theorem A without altering a target whose hom types are small. -/
set_option autoImplicit false
open CategoryTheory HomotopicalAlgebra
open DaggerOriginalProductGadget DaggerSSetGluing DaggerNerveHomotopy
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerNativeDualTheoremASmallTarget
noncomputable section

variable {A B : Type u} [Category.{u} A] [Category.{0} B] (F : A ⥤ B)

/-- Mathlib's map₂ raises only hom universes and retains the full original under-arrow data. -/
def underLift (b : B) : StructuredArrow b F ⥤
    StructuredArrow (ULiftHom.up.{0, u, u}.obj b) (F ⋙ ULiftHom.up.{0, u, u}) :=
  StructuredArrow.map₂ (F := 𝟭 A) (G := ULiftHom.up.{0, u, u})
    (𝟙 (ULiftHom.up.{0, u, u}.obj b)) (𝟙 (F ⋙ ULiftHom.up.{0, u, u}))

/-- This is Mathlib's existing equivalence criterion for the original structured comma. -/
instance underLift_isEquivalence (b : B) : (underLift F b).IsEquivalence := by
  let e : B ≌ ULiftHom.{u} B := ULiftHom.equiv
  have : (ULiftHom.up.{0, u, u} (C := B)).IsEquivalence := by
    change e.functor.IsEquivalence
    infer_instance
  exact StructuredArrow.isEquivalenceMap₂ _ _

/-- A weak terminal map stays weak after the exact hom-universe lift. -/
theorem lifted_under_point_GW (b : B)
    (hb : GW (pointMap (nerve (StructuredArrow b F)))) :
    GW (pointMap (nerve
      (StructuredArrow (ULiftHom.up.{0, u, u}.obj b) (F ⋙ ULiftHom.up.{0, u, u})))) := by
  let e := (underLift F b).asEquivalence
  have : WeakEquivalence (nerveMap e.inverse) := (weakEquivalence_iff_GW _).mpr
    (nerveMap_inverse_geometricW e.functor e.inverse
      (Relation.EqvGen.rel _ _ ⟨e.unitIso.inv⟩)
      (Relation.EqvGen.rel _ _ ⟨e.counitIso.hom⟩))
  have : WeakEquivalence (pointMap (nerve (StructuredArrow b F))) :=
    (weakEquivalence_iff_GW _).mpr hb
  have he : nerveMap e.inverse ≫ pointMap (nerve (StructuredArrow b F)) =
      pointMap (nerve
        (StructuredArrow (ULiftHom.up.{0, u, u}.obj b) (F ⋙ ULiftHom.up.{0, u, u}))) :=
    pointIsTerminal.hom_ext _ _
  apply (weakEquivalence_iff_GW _).mp
  rw [← he]
  infer_instance

/-- The lifted functor is weak under exactly the original structured-comma hypothesis. -/
theorem lifted_nerveMap_GW
    (hF : ∀ b : B, GW (pointMap (nerve (StructuredArrow b F)))) :
    GW (nerveMap (F ⋙ ULiftHom.up.{0, u, u})) := by
  apply DaggerNativeDualTheoremA.nerveMap_GW
  intro b
  exact lifted_under_point_GW F (ULiftHom.down.{0, u, u}.obj b) (hF _)

/-- The full original map on chains is weak; no simplices or arrows have been discarded. -/
theorem mixedMap_GW
    (hF : ∀ b : B, GW (pointMap (nerve (StructuredArrow b F)))) :
    GW (DaggerNativeSmallHomNerveLift.mixedMap F) := by
  have : WeakEquivalence (DaggerNativeSmallHomNerveLift.upMap B) := by
    change WeakEquivalence (DaggerNativeSmallHomNerveLift.iso B).hom
    infer_instance
  apply (weakEquivalence_iff_GW _).mp
  apply (weakEquivalence_postcomp_iff (DaggerNativeSmallHomNerveLift.mixedMap F)
    (DaggerNativeSmallHomNerveLift.upMap B)).mp
  rw [DaggerNativeSmallHomNerveLift.mixedMap_up]
  exact (weakEquivalence_iff_GW _).mpr (lifted_nerveMap_GW F hF)

end
end DaggerNativeDualTheoremASmallTarget
