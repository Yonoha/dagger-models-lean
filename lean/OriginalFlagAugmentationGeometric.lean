import OriginalFlagAugmentationToCenters
import NerveHomotopy

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial MonoidalCategory

universe u

namespace DaggerOriginalFlagFlankification

noncomputable section

open DaggerChosenRigidificationNecklace NecklaceCode DaggerNerveHomotopy

variable (X : SSet.{u}) (a b : X.obj (op ⦋0⦌)) (n : ℕ)

/-- The actual global zigzag is augmentation⋙centers ← flankification → Id. -/
theorem augmentationDegreeZigzag :
    NatTransZigzag (augmentation X a b n ⋙ centers X a b n) (𝟭 (Degree X a b n)) :=
  Relation.EqvGen.trans _ _ _
    (Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ ⟨toCenters X a b n⟩))
    (Relation.EqvGen.rel _ _ ⟨inclusion X a b n⟩)

theorem augmentationDiscreteZigzag :
    NatTransZigzag (centers X a b n ⋙ augmentation X a b n)
      (𝟭 (Discrete ((flagHom X a b).obj (op ⦋n⦌)))) :=
  Relation.EqvGen.rel _ _ ⟨(centersAugmentationIso X a b n).hom⟩

/-- Both raw endpoint equations retain the original beta; no raw symmetry is used. -/
def toCentersNerveHomotopy :
    SSet.Homotopy (nerveMap (flankification X a b n))
      (nerveMap (augmentation X a b n ⋙ centers X a b n)) :=
  natTransHomotopy (toCenters X a b n)

theorem toCentersNerveHomotopy_zero :
    SSet.ι₀ ≫ (toCentersNerveHomotopy X a b n).h =
      nerveMap (flankification X a b n) :=
  (toCentersNerveHomotopy X a b n).h₀

theorem toCentersNerveHomotopy_one :
    SSet.ι₁ ≫ (toCentersNerveHomotopy X a b n).h =
      nerveMap (augmentation X a b n ⋙ centers X a b n) :=
  (toCentersNerveHomotopy X a b n).h₁

/-- Every time-simplex object and arrow is the existing uncurried supplied NT. -/
theorem toCentersNerveHomotopy_app (k : SimplexCategoryᵒᵖ)
    (gamma : (nerve (Degree X a b n)).obj k)
    (s : (SSet.stdSimplex.obj ⦋1⦌).obj k) :
    (toCentersNerveHomotopy X a b n).h.app k (gamma, s) =
      ((SimplexCategory.toCat.map (SSet.stdSimplex.objEquiv s)).toFunctor.prod' gamma) ⋙
        Functor.uncurry.obj (ComposableArrows.mk₁ (toCenters X a b n)) := rfl

theorem toCentersNerveHomotopy_simplex {k l : SimplexCategoryᵒᵖ} (e : k ⟶ l)
    (gamma : (nerve (Degree X a b n)).obj k)
    (s : (SSet.stdSimplex.obj ⦋1⦌).obj k) :
    (nerve (Degree X a b n)).map e
        ((toCentersNerveHomotopy X a b n).h.app k (gamma, s)) =
      (toCentersNerveHomotopy X a b n).h.app l
        ((nerve (Degree X a b n)).map e gamma, (SSet.stdSimplex.obj ⦋1⦌).map e s) := rfl

/-- Realization/singularization is the existing R, with the original forward augmentation. -/
def augmentationHomotopyEquiv :
    SSet.HomotopyEquiv (R.obj (nerve (Degree X a b n)))
      (R.obj (nerve (Discrete ((flagHom X a b).obj (op ⦋n⦌))))) :=
  nerveHomotopyEquiv (augmentation X a b n) (centers X a b n)
    (augmentationDegreeZigzag X a b n) (augmentationDiscreteZigzag X a b n)

theorem augmentationHomotopyEquiv_hom :
    (augmentationHomotopyEquiv X a b n).hom = R.map (nerveMap (augmentation X a b n)) :=
  rfl

theorem augmentationHomotopyEquiv_inv :
    (augmentationHomotopyEquiv X a b n).inv = R.map (nerveMap (centers X a b n)) := rfl

def augmentationHomInvId :
    SSet.Homotopy
      (R.map (nerveMap (augmentation X a b n)) ≫ R.map (nerveMap (centers X a b n)))
      (𝟙 (R.obj (nerve (Degree X a b n)))) :=
  (augmentationHomotopyEquiv X a b n).homInvId

def augmentationInvHomId :
    SSet.Homotopy
      (R.map (nerveMap (centers X a b n)) ≫ R.map (nerveMap (augmentation X a b n)))
      (𝟙 (R.obj (nerve (Discrete ((flagHom X a b).obj (op ⦋n⦌)))))) :=
  (augmentationHomotopyEquiv X a b n).invHomId

/-- SAME original forward map; no input-nerve Kan hypothesis or replacement map. -/
theorem augmentation_geometric :
    SSet.KanComplex.W (TopCat.toSSet.map (SSet.toTop.map (nerveMap (augmentation X a b n)))) :=
  nerveMap_geometricW (augmentation X a b n) (centers X a b n)
    (augmentationDegreeZigzag X a b n) (augmentationDiscreteZigzag X a b n)

end

end DaggerOriginalFlagFlankification
