import ActualGeneralRightConeGadgetIndex
import ActualInnerIteratedGadgetShift

/-! Insert the unchanged right-cone simplex index into the actual iterated family. -/
set_option autoImplicit false
open CategoryTheory Opposite Simplicial DaggerModels OrdinaryRigidification
open DaggerOriginalCounitBNextConeEvaluationIndex
open DaggerOriginalCounitRightConeQRealizationAdjunction
open DaggerActualInnerIteratedGadgetData
universe u
namespace DaggerActualInnerIteratedRightConeIndex
noncomputable section

def base (X : SSet.{u}) (a b : X.obj (op ⦋0⦌)) :
    DaggerActualNecklaceConeGadgets.Over X a b ⥤ Over X a b where
  obj P := ⟨⟨P.code, 0⟩, P.map, P.first, P.last⟩
  map f := ⟨⟨f.hom.map, f.hom.first, f.hom.last⟩, f.w⟩
  map_id _ := by apply Over.Hom.ext; apply Hom.ext; rfl
  map_comp _ _ := by apply Over.Hom.ext; apply Hom.ext; rfl

def index (X : SSet.{u})
    (a b : X.obj (op ⦋0⦌)) :
    SimplexIndex (DaggerActualGeneralRightConeMapping.rightMapping X a b) ⥤ Over X a b :=
  DaggerActualGeneralRightConeGadgetIndex.index X a b ⋙ base _ a b

/-- The entire original cone simplex is retained without changing its degree or endpoints. -/
theorem index_obj_map (X : SSet.{u})
    (a b : X.obj (op ⦋0⦌))
    (σ : SimplexIndex (DaggerActualGeneralRightConeMapping.rightMapping X a b)) :
    ((index X a b).obj σ).map = (uliftYonedaEquiv σ.hom).val := rfl

/-- Every operator is the literal original coneMap of the same simplex operator. -/
theorem index_map_original (X : SSet.{u})
    (a b : X.obj (op ⦋0⦌))
    {σ τ : SimplexIndex (DaggerActualGeneralRightConeMapping.rightMapping X a b)}
    (f : σ ⟶ τ) :
    ((index X a b).map f).hom.map =
      DaggerOriginalCounitRightConeFunctor.coneMap.{u} f.left := rfl

abbrev DoubleComma (X : SSet.{u})
    (a b : X.obj (op ⦋0⦌)) :=
  Comma (index X a b) (DaggerActualInnerIteratedGadgetShift.inclusion X a b)

def toCones (X : SSet.{u})
    (a b : X.obj (op ⦋0⦌)) :
    DoubleComma X a b ⥤
      SimplexIndex (DaggerActualGeneralRightConeMapping.rightMapping X a b) := Comma.fst _ _

def toPositive (X : SSet.{u})
    (a b : X.obj (op ⦋0⦌)) :
    DoubleComma X a b ⥤ DaggerActualInnerIteratedGadgetShift.FibrantOver X a b := Comma.snd _ _

/-- Each original full comma arrow gives the exact comparison natural transformation. -/
def bridge (X : SSet.{u})
    (a b : X.obj (op ⦋0⦌)) :
    toCones X a b ⋙ index X a b ⟶
      toPositive X a b ⋙ DaggerActualInnerIteratedGadgetShift.inclusion X a b :=
  Comma.natTrans _ _

end
end DaggerActualInnerIteratedRightConeIndex
