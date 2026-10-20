import NativeOverNerveWeakContractibility

/-! A top element contracts the native nerve, using the existing nerve-homotopy theorem. -/
set_option autoImplicit false
open CategoryTheory Limits HomotopicalAlgebra
open DaggerSSetGluing DaggerOriginalProductGadget
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerNativeOrderTopNerveWeakContractibility
noncomputable section

theorem point_GW (P : Type u) [Preorder P] [OrderTop P] : GW (pointMap (nerve P)) := by
  let collapse : P ⥤ Discrete PUnit.{u + 1} := (Functor.const P).obj ⟨PUnit.unit⟩
  let center : Discrete PUnit.{u + 1} ⥤ P := (Functor.const _).obj ⊤
  let hP : 𝟭 P ⟶ collapse ⋙ center :=
    { app p := homOfLE (show p ≤ ⊤ from le_top)
      naturality _ _ _ := Subsingleton.elim _ _ }
  let h₀ : center ⋙ collapse ⟶ 𝟭 (Discrete PUnit.{u + 1}) :=
    { app p := eqToHom (Subsingleton.elim _ _)
      naturality _ _ _ := Subsingleton.elim _ _ }
  have : WeakEquivalence (nerveMap collapse) := (weakEquivalence_iff_GW _).mpr
    (DaggerNerveHomotopy.nerveMap_geometricW collapse center
      (Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ ⟨hP⟩))
      (Relation.EqvGen.rel _ _ ⟨h₀⟩))
  have he : nerveMap collapse ≫ (DaggerOriginalFlagFlankification.nerveDiscreteIso
      PUnit.{u + 1}).hom = pointMap (nerve P) := pointIsTerminal.hom_ext _ _
  apply (weakEquivalence_iff_GW _).mp
  rw [← he]
  infer_instance

end
end DaggerNativeOrderTopNerveWeakContractibility
