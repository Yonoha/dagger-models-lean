import OriginalGateNecklaceDiagram
import OriginalCutOverNaturality
import OriginalCutMapLaws

set_option autoImplicit false
open CategoryTheory Limits Opposite Simplicial
open DaggerChosenRigidificationNecklace
open DaggerChosenRigidificationNecklace.NecklaceCode
open DaggerOriginalFlagFlankification

universe u

namespace DaggerOriginalProductGadget

noncomputable section

variable {X : SSet.{u}} {a b v : X.obj (op ⦋0⦌)}

/-- Actual vertex images of a monomorphic necklace are injective. -/
theorem vertexImage_injective_of_mono (P : NecklacesOver X a b) (hP : Mono P.map) :
    Function.Injective (vertexImage P) := by
  intro k l h
  have h' := injective_of_mono (P.map.app (op ⦋0⦌)) h
  exact ULift.up_injective (P.code.verticesEquiv.symm.injective h')

/-- The over-X equation identifies the actual image of every source vertex. -/
theorem vertexImage_over_map {P Q : NecklacesOver X a b} (f : P ⟶ Q)
    (k : Fin (P.code.len + 1)) :
    vertexImage Q (orderMap f.hom.map k) = vertexImage P k := by
  change Q.map.app _ (Q.code.verticesEquiv.symm
    (ULift.up (orderMap f.hom.map k))) = P.map.app _ (P.code.verticesEquiv.symm (ULift.up k))
  rw [← necklaceMap_vertex_of_order f.hom.map k (orderMap f.hom.map k) rfl]
  exact congrFun (NatTrans.congr_app f.w _) _

/-- Choose the source joint above the specified gate; injectivity makes this choice unique. -/
def gateJoint (P : MonicGateNecklaces a b {v}) : Fin (P.obj.code.len + 1) :=
  Classical.choose (P.property.2 (Set.mem_singleton v))

theorem gateJoint_mem (P : MonicGateNecklaces a b {v}) :
    gateJoint P ∈ P.obj.code.joints :=
  (Classical.choose_spec (P.property.2 (Set.mem_singleton v))).1

theorem gateJoint_image (P : MonicGateNecklaces a b {v}) :
    vertexImage P.obj (gateJoint P) = v :=
  (Classical.choose_spec (P.property.2 (Set.mem_singleton v))).2

theorem gateJoint_unique (P : MonicGateNecklaces a b {v})
    (k : Fin (P.obj.code.len + 1)) (h : vertexImage P.obj k = v) : k = gateJoint P :=
  vertexImage_injective_of_mono P.obj P.property.1 (h.trans (gateJoint_image P).symm)

/-- Every original over-X arrow carries the uniquely specified gate joint to the same gate joint. -/
theorem gateJoint_naturality {P Q : MonicGateNecklaces a b {v}} (f : P ⟶ Q) :
    orderMap f.hom.hom.map (gateJoint P) = gateJoint Q :=
  gateJoint_unique Q _ ((vertexImage_over_map f.hom (gateJoint P)).trans (gateJoint_image P))

/-- The cut vertex is the originally specified gate, including gates equal to either endpoint. -/
theorem gateJoint_middle (P : MonicGateNecklaces a b {v}) :
    cutMiddleVertex P.obj (gateJoint P) = v := gateJoint_image P

/-- The original left cut with its endpoint equation transported to the specified gate. -/
def gateLeftOver (P : MonicGateNecklaces a b {v}) : NecklacesOver X a v where
  code := (cutLeftOver P.obj (gateJoint P)).code
  map := (cutLeftOver P.obj (gateJoint P)).map
  first := (cutLeftOver P.obj (gateJoint P)).first
  last := (cutLeftOver P.obj (gateJoint P)).last.trans (gateJoint_middle P)

/-- The original right cut with its endpoint equation transported from the specified gate. -/
def gateRightOver (P : MonicGateNecklaces a b {v}) : NecklacesOver X v b where
  code := (cutRightOver P.obj (gateJoint P)).code
  map := (cutRightOver P.obj (gateJoint P)).map
  first := (cutRightOver P.obj (gateJoint P)).first.trans (gateJoint_middle P)
  last := (cutRightOver P.obj (gateJoint P)).last

theorem gateLeftOver_mono (P : MonicGateNecklaces a b {v}) : Mono (gateLeftOver P).map := by
  have := P.property.1
  have : Mono (cutLeftι P.obj.code (gateJoint P)) :=
    inferInstanceAs (Mono (intervalι P.obj.code 0 (gateJoint P) (Fin.zero_le _)))
  change Mono (cutLeftι P.obj.code (gateJoint P) ≫ P.obj.map)
  infer_instance

theorem gateRightOver_mono (P : MonicGateNecklaces a b {v}) : Mono (gateRightOver P).map := by
  have := P.property.1
  have : Mono (cutRightι P.obj.code (gateJoint P)) :=
    inferInstanceAs (Mono (intervalι P.obj.code (gateJoint P) (Fin.last _) (Fin.le_last _)))
  change Mono (cutRightι P.obj.code (gateJoint P) ≫ P.obj.map)
  infer_instance

/-- Cutting each original arrow gives the same left interval restriction over X. -/
def gateLeftMap {P Q : MonicGateNecklaces a b {v}} (f : P ⟶ Q) :
    gateLeftOver P ⟶ gateLeftOver Q where
  hom := cutLeftHom f.hom.hom (gateJoint P) (gateJoint Q) (gateJoint_naturality f)
  w := cutLeftOver_naturality f.hom (gateJoint P) (gateJoint Q) (gateJoint_naturality f)

/-- Cutting each original arrow gives the same right interval restriction over X. -/
def gateRightMap {P Q : MonicGateNecklaces a b {v}} (f : P ⟶ Q) :
    gateRightOver P ⟶ gateRightOver Q where
  hom := cutRightHom f.hom.hom (gateJoint P) (gateJoint Q) (gateJoint_naturality f)
  w := cutRightOver_naturality f.hom (gateJoint P) (gateJoint Q) (gateJoint_naturality f)

end

end DaggerOriginalProductGadget
