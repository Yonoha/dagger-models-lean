import OriginalFlagNormalizedBeadCharts
import OriginalFlagFlankFibers

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial

universe u

namespace DaggerOriginalFlagFlankification

noncomputable section

open DaggerChosenRigidificationNecklace NecklaceCode

variable (X : SSet.{u}) (a b : X.obj (op ⦋0⦌)) (n : ℕ)

def TotallyNondegenerate (p : Degree X a b n) : Prop :=
  ∀ c : p.1.code.Bead, beadElement p.1 c ∈ X.nonDegenerate c.length

/-- The object uses SAME normOver and all literal images of the supplied original flag. -/
def normalizedDegreeObj (p : Degree X a b n) : Degree X a b n :=
  ⟨normOver p.1, originalNormalizedFlag p.1 p.2⟩

def normalizationDegreeArrow (p : Degree X a b n) : p ⟶ normalizedDegreeObj X a b n p :=
  CategoryOfElements.homMk (F := flagDegreeDiagram X a b (op ⦋n⦌)) p
    (normalizedDegreeObj X a b n p) (originalNormalization p.1) rfl

theorem normalizationDegreeArrow_whole (p : Degree X a b n) :
    (normalizationDegreeArrow X a b n p).val.hom.map =
      (originalNormalization p.1).hom.map := rfl

theorem normalizationDegreeArrow_triangle (p : Degree X a b n) :
    (normalizationDegreeArrow X a b n p).val.hom.map ≫
      (normalizedDegreeObj X a b n p).1.map = p.1.map :=
  originalNormalization_triangle p.1

theorem normalizationDegreeArrow_flag (p : Degree X a b n) :
    NecklaceCode.Flag.map (normalizationDegreeArrow X a b n p).val.hom p.2 =
      (normalizedDegreeObj X a b n p).2 := rfl

theorem normalizedDegreeObj_flanked (p : Degree X a b n) (hp : Flanked p.2) :
    Flanked (normalizedDegreeObj X a b n p).2 := originalNormalizedFlag_flanked p.1 p.2 hp

theorem normalizedDegreeObj_nondegenerate (p : Degree X a b n) :
    TotallyNondegenerate X a b n (normalizedDegreeObj X a b n p) :=
  normOver_beads_nondegenerate p.1

theorem normalizationDegreeArrow_class (p : Degree X a b n) :
    classOf X a b n p = classOf X a b n (normalizedDegreeObj X a b n p) :=
  classOf_map X a b n (normalizationDegreeArrow X a b n p)

variable (t : (flagHom X a b).obj (op ⦋n⦌))

/-- This remains in the SAME supplied augmentation fiber, not a replacement component. -/
def normalizedFiberObj (p : Fiber X a b n t) : Fiber X a b n t :=
  ⟨normalizedDegreeObj X a b n p.obj,
    (normalizationDegreeArrow_class X a b n p.obj).symm.trans p.property⟩

def normalizationFiberArrow (p : Fiber X a b n t) : p ⟶ normalizedFiberObj X a b n t p :=
  ObjectProperty.homMk (normalizationDegreeArrow X a b n p.obj)

def normalizedFlankedFiberObj (p : FlankedFiber X a b n t) : FlankedFiber X a b n t :=
  ⟨normalizedFiberObj X a b n t p.obj,
    normalizedDegreeObj_flanked X a b n p.obj.obj p.property⟩

def normalizationFlankedFiberArrow (p : FlankedFiber X a b n t) :
    p ⟶ normalizedFlankedFiberObj X a b n t p :=
  ObjectProperty.homMk (normalizationFiberArrow X a b n t p.obj)

theorem normalizedFlankedFiberObj_nondegenerate (p : FlankedFiber X a b n t) :
    TotallyNondegenerate X a b n (normalizedFlankedFiberObj X a b n t p).obj.obj :=
  normalizedDegreeObj_nondegenerate X a b n p.obj.obj

theorem normalizationFlankedFiberArrow_whole (p : FlankedFiber X a b n t) :
    (normalizationFlankedFiberArrow X a b n t p).hom.hom.val.hom.map =
      (originalNormalization p.obj.obj.1).hom.map := rfl

theorem normalizationFlankedFiberArrow_flag (p : FlankedFiber X a b n t) :
    NecklaceCode.Flag.map
      (normalizationFlankedFiberArrow X a b n t p).hom.hom.val.hom p.obj.obj.2 =
        (normalizedFlankedFiberObj X a b n t p).obj.obj.2 := rfl

end

end DaggerOriginalFlagFlankification
