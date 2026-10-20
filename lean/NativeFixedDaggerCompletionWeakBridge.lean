import OriginalFixedObjectDaggerCompletionQuillen

/-! The original dagger localization retains exactly the original ordinary localization Homs. -/
set_option autoImplicit false
open CategoryTheory HomotopicalAlgebra DaggerModels
open DaggerOriginalFixedObjectSimplicialCategories DaggerOriginalFixedObjectDaggerCategories
open DaggerOriginalFixedObjectGroupoidCompletionAdjunction
open DaggerOriginalSimplicialGroupoidCompletion
open scoped SSet.modelCategoryQuillen DaggerOriginalFixedObjectAmbientDaggerModel
universe u
namespace DaggerNativeFixedDaggerCompletionWeakBridge
noncomputable section

def fixedOfDagger (D : DaggerSimplicialCat.{u, u}) : FixedDaggerCategory D.Obj :=
  ⟨⟨D.toSimplicialCat.enriched⟩, D.daggerStructure⟩

theorem unit_weak_of_homs {O : Type u} (C : FixedDaggerCategory O)
    (hC : ∀ x y : O, WeakEquivalence (localizationHom (original O C.underlying) x y)) :
    WeakEquivalence (fixedDaggerLocalization C) := by
  rw [DaggerOriginalFixedObjectAmbientDaggerModel.weakEquivalence_iff_original]
  exact hC

theorem fixed_unit_weak (D : DaggerSimplicialCat.{u, u})
    (hD : ∀ x y : D.Obj, WeakEquivalence (localizationHom D.toSimplicialCat x y)) :
    WeakEquivalence (fixedDaggerLocalization (fixedOfDagger D)) :=
  unit_weak_of_homs (fixedOfDagger D) hD

end
end DaggerNativeFixedDaggerCompletionWeakBridge
