import ActualIteratedGadgetData
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-! The problem specifies the full positive-level inclusion and each original source map. -/
set_option autoImplicit false
open CategoryTheory Opposite Simplicial MonoidalCategory CartesianMonoidalCategory
open DaggerModels OrdinaryRigidification DaggerActualIteratedGadgetData
universe u
namespace DaggerActualIteratedFibrantStructuredArrowsChallenge

def statement : Prop :=
  ∀ (D : SimplicialCat.{u, u})
    (_hD : ∀ x y : D.Obj, SSet.KanComplex (x ⟶[SSet.{u}] y))
    (a b : (coherentNerve.obj D).obj (op ⦋0⦌))
    (O : Over (coherentNerve.obj D) a b),
    SSet.KanComplex.W (TopCat.toSSet.map (SSet.toTop.map (toUnit (nerve
      (StructuredArrow O
        (ObjectProperty.ι
          (fun P ↦ 0 < P.code.level : ObjectProperty (Over (coherentNerve.obj D) a b))))))))

end DaggerActualIteratedFibrantStructuredArrowsChallenge
