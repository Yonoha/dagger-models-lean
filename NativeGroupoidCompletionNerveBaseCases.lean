import OriginalInitialCategoryCompletionThin
import NativeOverNerveWeakContractibility

/-! Existing native localization and contraction data give exact nerve weak base cases. -/
set_option autoImplicit false
open CategoryTheory Limits HomotopicalAlgebra
open DaggerSSetGluing DaggerNerveHomotopy DaggerOriginalInitialCategoryCompletionThin
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerNativeGroupoidCompletionNerveBaseCases
noncomputable section

theorem nerveMap_weak_of_equivalence {C D : Type u} [Category.{u} C] [Category.{u} D]
    (F : C ⥤ D) [F.IsEquivalence] : WeakEquivalence (nerveMap F) := by
  let e := F.asEquivalence
  exact (weakEquivalence_iff_GW _).mpr
    (nerveMap_geometricW e.functor e.inverse
      (Relation.EqvGen.rel _ _ ⟨e.unitIso.inv⟩)
      (Relation.EqvGen.rel _ _ ⟨e.counitIso.hom⟩))

theorem unit_nerve_weak_of_groupoid (C : Type u) [Groupoid.{u} C] :
    WeakEquivalence (nerveMap (FreeGroupoid.of C)) := by
  let F := FreeGroupoid.of C
  let R := FreeGroupoid.lift (𝟭 C)
  have hC : F ⋙ R = 𝟭 C := FreeGroupoid.lift_spec (𝟭 C)
  have hG : R ⋙ F = 𝟭 (FreeGroupoid C) := FreeGroupoid.lift_id_comp_of
  exact (weakEquivalence_iff_GW _).mpr
    (nerveMap_geometricW F R (Relation.EqvGen.rel _ _ ⟨eqToHom hC⟩)
      (Relation.EqvGen.rel _ _ ⟨eqToHom hG⟩))

theorem unit_nerve_weak_of_initial {C : Type u} [Category.{u} C]
    (c : C) (hc : IsInitial c) : WeakEquivalence (nerveMap (FreeGroupoid.of C)) := by
  let F := FreeGroupoid.of C
  let R : FreeGroupoid C ⥤ C := (Functor.const _).obj c
  let hC : F ⋙ R ⟶ 𝟭 C :=
    { app x := hc.to x
      naturality _ _ _ := hc.hom_ext _ _ }
  let hG : R ⋙ F ⟶ 𝟭 (FreeGroupoid C) :=
    { app x := (completedContraction c hc).hom.app x
      naturality x y f := by
        change F.map (𝟙 c) ≫ (completedContraction c hc).hom.app y =
          (completedContraction c hc).hom.app x ≫ f
        rw [F.map_id]
        exact (completedContraction c hc).hom.naturality f }
  exact (weakEquivalence_iff_GW _).mpr
    (nerveMap_geometricW F R (Relation.EqvGen.rel _ _ ⟨hC⟩)
      (Relation.EqvGen.rel _ _ ⟨hG⟩))

end
end DaggerNativeGroupoidCompletionNerveBaseCases
