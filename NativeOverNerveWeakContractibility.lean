import NativeDualTheoremAProjections

/-! The native over-category contracts to its actual terminal identity arrow. -/
set_option autoImplicit false
open CategoryTheory Limits Opposite HomotopicalAlgebra
open DaggerSSetGluing DaggerOriginalProductGadget
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerNativeOverNerveWeakContractibility
noncomputable section

/-- The original identity arrow is a terminal object of the actual over-category. -/
theorem point_GW {D : Type u} [Category.{u} D] (d : D) :
    GW (pointMap (nerve (Over d))) := by
  let E := Over d
  let e : E := Over.mk (𝟙 d)
  let he : IsTerminal e := CostructuredArrow.mkIdTerminal
  let collapse : E ⥤ Discrete PUnit.{u + 1} := (Functor.const E).obj ⟨PUnit.unit⟩
  let center : Discrete PUnit.{u + 1} ⥤ E := (Functor.const _).obj e
  let hE : 𝟭 E ⟶ collapse ⋙ center :=
    { app P := he.from P
      naturality {P Q} f := he.hom_ext _ _ }
  let hP : center ⋙ collapse ⟶ 𝟭 (Discrete PUnit.{u + 1}) :=
    { app P := eqToHom (Subsingleton.elim _ _)
      naturality {P Q} f := Subsingleton.elim _ _ }
  have : WeakEquivalence (nerveMap collapse) := (weakEquivalence_iff_GW _).mpr
    (DaggerNerveHomotopy.nerveMap_geometricW collapse center
      (Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ ⟨hE⟩))
      (Relation.EqvGen.rel _ _ ⟨hP⟩))
  have hm : nerveMap collapse ≫ (DaggerOriginalFlagFlankification.nerveDiscreteIso
      PUnit.{u + 1}).hom = pointMap (nerve E) := pointIsTerminal.hom_ext _ _
  apply (weakEquivalence_iff_GW _).mp
  rw [← hm]
  infer_instance

end
end DaggerNativeOverNerveWeakContractibility
