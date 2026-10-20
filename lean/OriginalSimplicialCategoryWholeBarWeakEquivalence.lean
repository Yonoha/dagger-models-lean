import OriginalSimplicialCategoryWholeBarContraction

/-!
# The whole original bar is weakly equivalent to its original object-indexed points

The target is the native coproduct of standard points indexed by the unchanged
original objects. The actual component augmentations and sections assemble by
native coproduct maps. The whole original homotopy gives a homotopy equivalence
after realization and singular, using reversal only in its fibrant Kan target.
-/
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Opposite Simplicial DaggerModels
open HomotopicalAlgebra
open DaggerOriginalSimplicialCategoryBarConstruction
open DaggerOriginalSimplicialCategoryBarContraction
open DaggerOriginalSimplicialCategoryBarWeakContractibility
open DaggerOriginalSimplicialCategoryWholeBarContraction
universe u
namespace DaggerOriginalSimplicialCategoryWholeBarWeakEquivalence
noncomputable section

/-- The actual standard points are indexed by every unchanged original object. -/
def objectPoints (C : SimplicialCat.{u, u}) : SSet.{u} :=
  ∐ (fun _ : C.Obj ↦ (Δ[0] : SSet.{u}))

/-- The actual native coproduct of all original component augmentations. -/
def wholeBarAugmentation (C : SimplicialCat.{u, u}) : bar C ⟶ objectPoints C :=
  Limits.Sigma.map (barAugmentation C)

/-- The actual native coproduct of sections at the original identity-arrow vertices. -/
def wholeBarPointSection (C : SimplicialCat.{u, u}) : objectPoints C ⟶ bar C :=
  Limits.Sigma.map (barPointSection C)

/-- The original augmentation-section composite is the actual whole terminal endomorphism. -/
theorem wholeBarAugmentation_section (C : SimplicialCat.{u, u}) :
    wholeBarAugmentation C ≫ wholeBarPointSection C = wholeBarTerminalEnd C := by
  change Limits.Sigma.map (barAugmentation C) ≫ Limits.Sigma.map (barPointSection C) = _
  rw [Limits.Sigma.map_comp_map]
  apply congrArg Limits.Sigma.map
  funext y
  exact (barAugmentation_section C y).trans (terminalBarEnd_eq_const C y).symm

/-- The original section-augmentation composite is identity on every original object point. -/
theorem wholeBarPointSection_augmentation (C : SimplicialCat.{u, u}) :
    wholeBarPointSection C ≫ wholeBarAugmentation C = 𝟙 (objectPoints C) := by
  change Limits.Sigma.map (barPointSection C) ≫ Limits.Sigma.map (barAugmentation C) = _
  simp only [Limits.Sigma.map_comp_map, barPointSection_augmentation, Limits.Sigma.map_id]
  rfl

/-- The whole original augmentation becomes an actual native homotopy equivalence. -/
def wholeBarAugmentationHomotopyEquiv (C : SimplicialCat.{u, u}) :
    (DaggerNerveHomotopy.R.obj (bar C)).HomotopyEquiv
      (DaggerNerveHomotopy.R.obj (objectPoints C)) where
  hom := DaggerNerveHomotopy.R.map (wholeBarAugmentation C)
  inv := DaggerNerveHomotopy.R.map (wholeBarPointSection C)
  homInvId := by
    let h := SSet.Subcomplex.RelativeMorphism.Homotopy.symm
      (wholeBarHomotopy C).toTop.toSSet
    refine SSet.Homotopy.congr h ?_ ?_
    · change DaggerNerveHomotopy.R.map (wholeBarTerminalEnd C) = _
      rw [← DaggerNerveHomotopy.R.map_comp, wholeBarAugmentation_section]
    · exact DaggerNerveHomotopy.R.map_id _
  invHomId := by
    apply SSet.Subcomplex.RelativeMorphism.Homotopy.ofEq
    rw [← DaggerNerveHomotopy.R.map_comp, wholeBarPointSection_augmentation,
      DaggerNerveHomotopy.R.map_id]

/-- The original whole bar augmentation to its actual object-indexed points is weak. -/
theorem wholeBarAugmentation_weakEquivalence (C : SimplicialCat.{u, u}) :
    WeakEquivalence (wholeBarAugmentation C) := by
  apply (SSet.modelCategoryQuillen.weakEquivalence_iff _).mpr
  apply (TopCat.modelCategory.weakEquivalence_iff _).mpr
  exact SSet.KanComplex.W.homotopyEquivHom (wholeBarAugmentationHomotopyEquiv C)

end
end DaggerOriginalSimplicialCategoryWholeBarWeakEquivalence
