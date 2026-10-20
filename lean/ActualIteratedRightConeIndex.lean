import ActualRightConeGadgetIndex
import ActualIteratedGadgetShift

/-! Insert the unchanged right-cone simplex index into the actual iterated family. -/
set_option autoImplicit false
open CategoryTheory Opposite Simplicial DaggerModels OrdinaryRigidification
open DaggerOriginalCounitBNextConeEvaluationIndex
open DaggerOriginalCounitRightConeQRealizationAdjunction
open DaggerActualIteratedGadgetData
universe u
namespace DaggerActualIteratedRightConeIndex
noncomputable section

def base (X : SSet.{u}) (a b : X.obj (op ⦋0⦌)) :
    DaggerActualNecklaceConeGadgets.Over X a b ⥤ Over X a b where
  obj P := ⟨⟨P.code, 0⟩, P.map, P.first, P.last⟩
  map f := ⟨⟨f.hom.map, f.hom.first, f.hom.last⟩, f.w⟩
  map_id _ := by apply Over.Hom.ext; apply Hom.ext; rfl
  map_comp _ _ := by apply Over.Hom.ext; apply Hom.ext; rfl

def index (D : SimplicialCat.{u, u})
    (a b : (coherentNerve.obj D).obj (op ⦋0⦌)) :
    SimplexIndex (rightConeSimplices D a b) ⥤ Over (coherentNerve.obj D) a b :=
  DaggerActualRightConeGadgetIndex.index D a b ⋙ base _ a b

/-- The entire original cone simplex is retained without changing its degree or endpoints. -/
theorem index_obj_map (D : SimplicialCat.{u, u})
    (a b : (coherentNerve.obj D).obj (op ⦋0⦌))
    (σ : SimplexIndex (rightConeSimplices D a b)) :
    ((index D a b).obj σ).map = (uliftYonedaEquiv σ.hom).val := rfl

/-- Every operator is the literal original coneMap of the same simplex operator. -/
theorem index_map_original (D : SimplicialCat.{u, u})
    (a b : (coherentNerve.obj D).obj (op ⦋0⦌))
    {σ τ : SimplexIndex (rightConeSimplices D a b)} (f : σ ⟶ τ) :
    ((index D a b).map f).hom.map =
      DaggerOriginalCounitRightConeFunctor.coneMap.{u} f.left := rfl

abbrev DoubleComma (D : SimplicialCat.{u, u})
    (a b : (coherentNerve.obj D).obj (op ⦋0⦌)) :=
  Comma (index D a b) (DaggerActualIteratedGadgetShift.inclusion D a b)

def toCones (D : SimplicialCat.{u, u})
    (a b : (coherentNerve.obj D).obj (op ⦋0⦌)) :
    DoubleComma D a b ⥤ SimplexIndex (rightConeSimplices D a b) := Comma.fst _ _

def toPositive (D : SimplicialCat.{u, u})
    (a b : (coherentNerve.obj D).obj (op ⦋0⦌)) :
    DoubleComma D a b ⥤ DaggerActualIteratedGadgetShift.FibrantOver D a b := Comma.snd _ _

/-- Each original full comma arrow gives the exact comparison natural transformation. -/
def bridge (D : SimplicialCat.{u, u})
    (a b : (coherentNerve.obj D).obj (op ⦋0⦌)) :
    toCones D a b ⋙ index D a b ⟶
      toPositive D a b ⋙ DaggerActualIteratedGadgetShift.inclusion D a b := Comma.natTrans _ _

end
end DaggerActualIteratedRightConeIndex
