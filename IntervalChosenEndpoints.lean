import IntervalChosenGeometric

set_option autoImplicit false

open CategoryTheory EnrichedCategory Opposite Simplicial

universe u

namespace DaggerOriginalIntervalChosenHom

noncomputable section

open DaggerChosenRigidificationNecklace hiding E
open DaggerIntervalNecklaceCompletion

abbrev boolVertex (a : Bool) : E.{u}.obj (op ⦋0⦌) := endpoint a

def boolObject (a : Bool) : (C.{u}.obj E).Obj := RV E (boolVertex a)

theorem bool_sourceVertex (a : Bool) : sourceVertex (boolObject.{u} a) = boolVertex a :=
  (RV E).symm_apply_apply (boolVertex a)

/-- Includes 00/01/10/11, without restricting the preceding all-object theorem. -/
def boolHomContractible (a b : Bool) :
    SSet.Contractible (originalHom (boolObject.{u} a) (boolObject b)) :=
  originalIntervalHomContractible _ _

theorem boolHom_geometric (a b : Bool) :
    SSet.KanComplex.W (TopCat.toSSet.map (SSet.toTop.map
      (originalCollapse (boolObject.{u} a) (boolObject b)))) :=
  originalIntervalHom_geometric _ _

theorem boolCenter_edge (a b : Bool) :
    originalCenter (boolObject.{u} a) (boolObject b) = edgeCenter (boolVertex a) (boolVertex b) :=
  by
  rw [originalCenter_edge]
  have transport : ∀ (a' b' : E.{u}.obj (op ⦋0⦌))
      (ha : a' = boolVertex a) (hb : b' = boolVertex b),
      (targetHomTransport (congrArg (RV E) ha) (congrArg (RV E) hb)).app (op ⦋0⦌)
        (edgeCenter a' b') = edgeCenter (boolVertex a) (boolVertex b) := by
    intro a' b' ha hb
    cases ha
    cases hb
    rfl
  exact transport _ _ (bool_sourceVertex a) (bool_sourceVertex b)

end

end DaggerOriginalIntervalChosenHom
