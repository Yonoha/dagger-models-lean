import ActualInnerNecklaceWeightComparison

/-! The original flag-to-Hom isomorphisms respect all actual necklace maps and augmentations. -/
set_option autoImplicit false
open CategoryTheory Opposite Simplicial HomotopicalAlgebra DaggerModels OrdinaryRigidification
open DaggerChosenRigidificationNecklace DaggerOriginalFlagFlankification
open DaggerActualInnerGadgetHomAugmentation DaggerActualInnerNecklaceWeightComparison
open DaggerNativeSimplicialReplacement DaggerNativeSimplicialReplacementWeightsChange
open DaggerActualInnerGadgetWeightedReindex DaggerSSetGluing
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerActualInnerNecklaceWeightNaturality
noncomputable section

variable (X : SSet.{u}) (a b : X.obj (op ⦋0⦌))

/-- These are the original whole flag-to-C(T) Hom isomorphisms on the exact necklace objects. -/
def comparison : NecklacesOver.flagDiagram X a b ⟶
    DaggerActualInnerIteratedGadgetNecklaceComparison.inclusion X a b ⋙ diagram X a b where
  app P := (necklaceOriginalOuterHomIso P.code).hom
  naturality {P Q} f := by
    let U : NecklacesOver Q.code.toSSet Q.code.first Q.code.last :=
      ⟨P.code, f.hom.map, f.hom.first, f.hom.last⟩
    let h : U ⟶ self Q.code := ⟨f.hom, Category.comp_id _⟩
    have hn := chosenFlagLeg_naturality h
    rw [self_leg] at hn
    exact hn.trans (leg_factor U).symm

/-- Preserve each whole original flag and whole original necklace chain
in the weighted gadget bar. -/
def barMap := diagonalChange (comparison X a b) ≫ necklaceMap X a b

/-- Both exact comparisons are weak, using original P2
and the proved original necklace inclusion. -/
theorem barMap_GW : GW (barMap X a b) := by
  have : WeakEquivalence (diagonalChange (comparison X a b)) :=
    (weakEquivalence_iff_GW _).mpr (diagonalChange_GW (comparison X a b)
      (DaggerActualNecklaceFlagAugmentation.projection_GW X a b)
      (diagonalProjection_GW
        (DaggerActualInnerIteratedGadgetNecklaceComparison.inclusion X a b ⋙ diagram X a b)
        (fun P ↦ diagram_point_GW X a b
          ((DaggerActualInnerIteratedGadgetNecklaceComparison.inclusion X a b).obj P))))
  have : WeakEquivalence (necklaceMap X a b) :=
    (weakEquivalence_iff_GW _).mpr (necklaceMap_GW X a b)
  exact (weakEquivalence_iff_GW _).mp (show WeakEquivalence
    (diagonalChange (comparison X a b) ≫ necklaceMap X a b) from inferInstance)

/-- The resulting augmentation is exactly the original P2 Hom augmentation on the entire flag. -/
theorem augmentation_square : barMap X a b ≫ toOriginalHom X a b =
    diagonalAugmentation (NecklacesOver.flagDiagram X a b)
      (DaggerActualNecklaceFlagAugmentation.augmentation X a b) ≫
        (flagOriginalHomIso X a b).hom := by
  apply NatTrans.ext
  funext q x
  rcases x with ⟨c, t⟩
  change ((necklaceOriginalOuterHomIso (c.obj 0).code).hom ≫
      leg X a b ((DaggerActualInnerIteratedGadgetNecklaceComparison.inclusion X a b).obj
        (c.obj 0))).app q t =
    (flagOriginalHomIso X a b).hom.app q
      (Quot.mk (flagRelation X a b q) ⟨c.obj 0, t⟩)
  rw [leg_factor]
  exact (flagOriginalHomIso_raw X a b (c.obj 0) q t).symm

end
end DaggerActualInnerNecklaceWeightNaturality
