import OriginalSimplicialCategoryBarContraction
import TopCatModelCategory.SSet.Contractible

/-!
# Weak contractibility of every actual original bar component

Realize the actual identity-to-constant simplicial homotopy and apply the native
singular functor. Reverse the homotopy in the resulting Kan complex. This gives a native
homotopy equivalence after realization and singular, hence the actual original
augmentation to the standard point is a weak equivalence.
-/
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Opposite Simplicial DaggerModels
open HomotopicalAlgebra
open DaggerOriginalSimplicialCategoryBarConstruction
open DaggerOriginalSimplicialCategoryBarContraction
universe u
namespace DaggerOriginalSimplicialCategoryBarWeakContractibility
noncomputable section

/-- The actual original bar component's native augmentation to the standard point. -/
def barAugmentation (C : SimplicialCat.{u, u}) (y : C.Obj) :
    barComponent C y ⟶ Δ[0] := SSet.stdSimplex.isTerminalObj₀.from (barComponent C y)

/-- The section selects exactly the original identity-arrow vertex. -/
def barPointSection (C : SimplicialCat.{u, u}) (y : C.Obj) :
    Δ[0] ⟶ barComponent C y := SSet.const (terminalBarPoint C y)

/-- The composite on the original component is exactly its native constant vertex map. -/
theorem barAugmentation_section (C : SimplicialCat.{u, u}) (y : C.Obj) :
    barAugmentation C y ≫ barPointSection C y = SSet.const (terminalBarPoint C y) :=
  SSet.comp_const _ _

/-- The composite on the actual standard point is its identity. -/
theorem barPointSection_augmentation (C : SimplicialCat.{u, u}) (y : C.Obj) :
    barPointSection C y ≫ barAugmentation C y = 𝟙 Δ[0] :=
  SSet.stdSimplex.isTerminalObj₀.hom_ext _ _

/-- Realization and singular of the actual original augmentation is a homotopy equivalence. -/
def barAugmentationHomotopyEquiv (C : SimplicialCat.{u, u}) (y : C.Obj) :
    (DaggerNerveHomotopy.R.obj (barComponent C y)).HomotopyEquiv
      (DaggerNerveHomotopy.R.obj Δ[0]) where
  hom := DaggerNerveHomotopy.R.map (barAugmentation C y)
  inv := DaggerNerveHomotopy.R.map (barPointSection C y)
  homInvId := by
    let h := SSet.Subcomplex.RelativeMorphism.Homotopy.symm
      (barContraction C y).toTop.toSSet
    refine SSet.Homotopy.congr h ?_ ?_
    · change DaggerNerveHomotopy.R.map (SSet.const (terminalBarPoint C y)) = _
      rw [← DaggerNerveHomotopy.R.map_comp, barAugmentation_section]
    · exact DaggerNerveHomotopy.R.map_id _
  invHomId := by
    apply SSet.Subcomplex.RelativeMorphism.Homotopy.ofEq
    rw [← DaggerNerveHomotopy.R.map_comp, barPointSection_augmentation,
      DaggerNerveHomotopy.R.map_id]

/-- The actual original bar component is weakly equivalent to the native standard point. -/
theorem barAugmentation_weakEquivalence (C : SimplicialCat.{u, u}) (y : C.Obj) :
    WeakEquivalence (barAugmentation C y) := by
  apply (SSet.modelCategoryQuillen.weakEquivalence_iff _).mpr
  apply (TopCat.modelCategory.weakEquivalence_iff _).mpr
  exact SSet.KanComplex.W.homotopyEquivHom (barAugmentationHomotopyEquiv C y)

end
end DaggerOriginalSimplicialCategoryBarWeakContractibility
