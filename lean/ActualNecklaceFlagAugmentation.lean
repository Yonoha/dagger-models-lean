import ActualNecklaceFlagReplacement

/-! The whole necklace replacement augmentation is exactly the original P2 augmentation. -/
set_option autoImplicit false
open CategoryTheory Opposite Simplicial HomotopicalAlgebra
open DaggerChosenRigidificationNecklace DaggerOriginalFlagFlankification
open DaggerNativeSimplicialReplacement DaggerActualNecklaceFlagReplacement
open DaggerSSetGluing
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerActualNecklaceFlagAugmentation
noncomputable section

variable (X : SSet.{u}) (a b : X.obj (op ⦋0⦌))

def augmentation : NecklacesOver.flagDiagram X a b ⟶
    (Functor.const (NecklacesOver X a b)).obj (flagHom X a b) := (flagCocone X a b).ι

/-- The whole original epsilon is precisely this replacement augmentation after the full isomorphism. -/
theorem augmentation_original : (diagonalIso X a b).hom ≫
    diagonalAugmentation (NecklacesOver.flagDiagram X a b) (augmentation X a b) =
      originalEpsilon X a b := by
  apply NatTrans.ext
  rfl

/-- The original P2 theorem proves this exact augmentation weak without an extra comparison premise. -/
theorem augmentation_GW : GW
    (diagonalAugmentation (NecklacesOver.flagDiagram X a b) (augmentation X a b)) := by
  have : WeakEquivalence (diagonalIso X a b).hom := inferInstance
  apply (weakEquivalence_iff_GW _).mp
  apply (weakEquivalence_precomp_iff (diagonalIso X a b).hom
    (diagonalAugmentation (NecklacesOver.flagDiagram X a b) (augmentation X a b))).mp
  rw [augmentation_original]
  exact (weakEquivalence_iff_GW _).mpr (originalP2_both_GW X a b).1

/-- The corresponding whole-chain projection is exactly the already proved original P2 projection. -/
theorem projection_GW : GW (diagonalProjection (NecklacesOver.flagDiagram X a b)) := by
  have : WeakEquivalence (diagonalIso X a b).hom := inferInstance
  apply (weakEquivalence_iff_GW _).mp
  apply (weakEquivalence_precomp_iff (diagonalIso X a b).hom
    (diagonalProjection (NecklacesOver.flagDiagram X a b))).mp
  rw [projection_original]
  exact (weakEquivalence_iff_GW _).mpr (originalP2_both_GW X a b).2

end
end DaggerActualNecklaceFlagAugmentation
