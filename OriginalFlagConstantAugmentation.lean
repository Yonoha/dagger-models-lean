import OriginalFlagDiscreteNerve
import OriginalFlagAugmentationGeometric

set_option autoImplicit false

open CategoryTheory Opposite Simplicial
open scoped SSet.modelCategoryQuillen

universe u

namespace DaggerOriginalFlagFlankification

noncomputable section

open DaggerChosenRigidificationNecklace DaggerNerveHomotopy

variable (X : SSet.{u}) (a b : X.obj (op ⦋0⦌)) (n : ℕ)

/-- SAME original augmentation followed by the genuine discrete-nerve target iso. -/
def constantAugmentation :
    nerve (Degree X a b n) ⟶ constantSSet ((flagHom X a b).obj (op ⦋n⦌)) :=
  nerveMap (augmentation X a b n) ≫
    (nerveDiscreteIso ((flagHom X a b).obj (op ⦋n⦌))).hom

theorem constantAugmentation_factor :
    constantAugmentation X a b n = nerveMap (augmentation X a b n) ≫
      (nerveDiscreteIso ((flagHom X a b).obj (op ⦋n⦌))).hom := rfl

/-- Every simplex retains the literal original quotient representative at object0. -/
theorem constantAugmentation_app (k : SimplexCategoryᵒᵖ)
    (gamma : (nerve (Degree X a b n)).obj k) :
    (constantAugmentation X a b n).app k gamma = classOf X a b n (gamma.obj 0) := rfl

/-- Every simplex operator retains its actual image of object0. -/
theorem constantAugmentation_operator {k l : SimplexCategoryᵒᵖ} (alpha : k ⟶ l)
    (gamma : (nerve (Degree X a b n)).obj k) :
    (constantAugmentation X a b n).app l ((nerve (Degree X a b n)).map alpha gamma) =
      classOf X a b n (gamma.obj (alpha.unop.toOrderHom 0)) := rfl

theorem constantAugmentation_naturality {k l : SimplexCategoryᵒᵖ} (alpha : k ⟶ l)
    (gamma : (nerve (Degree X a b n)).obj k) :
    (constantAugmentation X a b n).app l ((nerve (Degree X a b n)).map alpha gamma) =
      (constantAugmentation X a b n).app k gamma :=
  congrFun ((constantAugmentation X a b n).naturality alpha) gamma

theorem constantAugmentation_R_factor :
    R.map (constantAugmentation X a b n) = R.map (nerveMap (augmentation X a b n)) ≫
      R.map ((nerveDiscreteIso ((flagHom X a b).obj (op ⦋n⦌))).hom) :=
  Functor.map_comp R _ _

/-- The geometric row W follows from the SAME accepted augmentation and mapped target iso. -/
theorem constantAugmentation_geometric :
    SSet.KanComplex.W
      (TopCat.toSSet.map (SSet.toTop.map (constantAugmentation X a b n))) := by
  change SSet.KanComplex.W (R.map (constantAugmentation X a b n))
  rw [constantAugmentation_R_factor]
  exact SSet.KanComplex.W.comp _ _ (augmentation_geometric X a b n)
    (SSet.KanComplex.W.of_iso _)

end

end DaggerOriginalFlagFlankification
