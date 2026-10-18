import ActualIteratedGadgetHomAugmentationWeakness

/-! The exact cone-weighted replacement augmentation factors through the original Q realization map. -/
set_option autoImplicit false
open CategoryTheory Opposite Simplicial DaggerModels OrdinaryRigidification
open DaggerOriginalCounitRightConeQRealizationAdjunction
open DaggerOriginalCounitBNextConeEvaluationIndex
open DaggerOriginalCounitBNextConeRealizationFactorization
open DaggerActualIteratedGadgetHomAugmentation DaggerNativeSimplicialReplacement
open DaggerActualIteratedGadgetWeightedReindex DaggerSSetGluing
universe u
namespace DaggerActualConeWeightedRealizationFactorization
noncomputable section

variable (D : SimplicialCat.{u, u})
variable (a b : (coherentNerve.obj D).obj (op ⦋0⦌))

abbrev Index := ULiftHom.{u} (SimplexIndex (rightConeSimplices D a b))

def weights : Index D a b ⥤ SSet.{u} :=
  DaggerActualIteratedConeIndexWeakness.raisedIndex D a b ⋙ diagram (coherentNerve.obj D) a b

/-- Keep the entire original Q-realization simplex leg at the unchanged cone simplex. -/
def realizationLeg (σ : Index D a b) : (weights D a b).obj σ ⟶
    realization.obj (rightConeSimplices D a b) :=
  realizationUnit.app (ULiftHom.down.{0, u, u}.obj σ).left ≫
    realization.map (ULiftHom.down.{0, u, u}.obj σ).hom

/-- Every original cone operator commutes with the literal realization cocone. -/
def augmentation : weights D a b ⟶ (Functor.const (Index D a b)).obj
    (realization.obj (rightConeSimplices D a b)) where
  app := realizationLeg D a b
  naturality {_σ _τ} f := (simplexCocone (rightConeSimplices D a b)).ι.naturality f.down

/-- This is the unchanged augmentation of the full cone-weighted replacement to Q realization. -/
def toRealization : DaggerBisimplicialDiagonal.diag (replacement (weights D a b)) ⟶
    realization.obj (rightConeSimplices D a b) :=
  diagonalAugmentation (weights D a b) (augmentation D a b)

/-- Each entire original cone cell factors through the exact original coneRigidificationMap. -/
theorem augmentation_factor : toRealization D a b ≫ coneRigidificationMap D a b =
    coneMap D a b ≫ toOriginalHom (coherentNerve.obj D) a b := by
  apply NatTrans.ext
  funext q x
  rcases x with ⟨c, t⟩
  let σ := ULiftHom.down.{0, u, u}.obj (c.obj 0)
  change ((realizationUnit.app σ.left ≫ realization.map σ.hom) ≫
      coneRigidificationMap D a b).app q t =
    (leg (coherentNerve.obj D) a b
      ((DaggerActualIteratedRightConeIndex.index D a b).obj σ)).app q t
  rw [Category.assoc, coneRigidificationMap_leg]
  rfl

/-- The actual composite through Q realization is weak, without supplying either comparison leg. -/
theorem composite_GW (hD : ∀ x y : D.Obj, SSet.KanComplex (x ⟶[SSet.{u}] y)) :
    GW (toRealization D a b ≫ coneRigidificationMap D a b) := by
  rw [augmentation_factor]
  exact DaggerActualIteratedGadgetHomAugmentationWeakness.cone_augmentation_GW D hD a b

end
end DaggerActualConeWeightedRealizationFactorization
