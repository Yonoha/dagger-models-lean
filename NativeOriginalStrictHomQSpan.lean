import NativeOriginalC2QSingularSpan
import OriginalStrictDaggerGroupoidMappingAction

/-! BOTH old Q-span legs apply to the EXACT original strict Hom/Sigma, with no extra premise. -/
set_option autoImplicit false
open CategoryTheory Simplicial HomotopicalAlgebra DaggerModels
open DaggerOriginalSimplicialGroupoidCompletionUniversal
open DaggerOriginalStrictDaggerGroupoidMappingAction
open DaggerOriginalStrictSimplicialGroupoidMappingKan DaggerNativeOriginalC2QSingularSpan
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerNativeOriginalStrictHomQSpan
noncomputable section

variable (C : DaggerSimplicialCat.{u, u}) (hC : IsStrictGroupoid C.toSimplicialCat)
variable (x y : C.Obj)

theorem both_weak :
    WeakEquivalence (constantsAction (strictMappingAction C hC x y)).hom ∧
      WeakEquivalence (singularActionComparison (strictMappingAction C hC x y)).hom := by
  have : (strictMappingAction C hC x y).V.KanComplex := strictHom_kan C.toSimplicialCat hC x y
  exact ⟨constantsAction_weak _, singularActionComparison_weak _⟩

theorem both_realized_EC2_weak :
    WeakEquivalence (realizedConstants (strictMappingAction C hC x y)) ∧
      WeakEquivalence (realizedSingularComparison (strictMappingAction C hC x y)) := by
  have : (strictMappingAction C hC x y).V.KanComplex := strictHom_kan C.toSimplicialCat hC x y
  exact ⟨realizedConstants_weak _, realizedSingularComparison_weak _⟩

end
end DaggerNativeOriginalStrictHomQSpan
