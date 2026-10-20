import ChosenNecklaceEnrichment
import ChosenNecklaceFlags

open CategoryTheory Limits Opposite Simplicial

universe u

namespace DaggerChosenRigidificationNecklace.NecklaceThickening

noncomputable section

open NecklaceCode

def OuterPath (T : NecklaceCode) : Type u :=
  JointPath (ULift.up (0 : Fin (T.len + 1))) (ULift.up (Fin.last T.len))

instance (T : NecklaceCode) : Category (OuterPath.{u} T) :=
  inferInstanceAs (Category (JointPath _ _))

variable (T : NecklaceCode)

def flagToNerve {n : ℕ} (F : NecklaceCode.Flag.{u} T n) :
    (nerve (OuterPath.{u} T)).obj (op ⦋n⦌) where
  obj i :=
    { I := F.chain i
      left := F.chain.monotone (Fin.zero_le i) (F.joints _ T.first_mem)
      right := F.chain.monotone (Fin.zero_le i) (F.joints _ T.last_mem)
      left_le v _ := Fin.zero_le v.down
      le_right v _ := Fin.le_last v.down
      joints j hj _ _ := F.chain.monotone (Fin.zero_le i) (F.joints _ hj) }
  map h := ⟨⟨⟨F.chain.monotone (leOfHom h)⟩⟩⟩

def nerveToFlag {n : ℕ} (F : (nerve (OuterPath.{u} T)).obj (op ⦋n⦌)) :
    NecklaceCode.Flag.{u} T n where
  chain :=
    { toFun i := (F.obj i).I
      monotone' _i _j h := (F.map (homOfLE h)).1.1.1 }
  joints v hv := (F.obj 0).joints v.down hv (Fin.zero_le v.down) (Fin.le_last v.down)

def outerFlagEquiv (n : ℕ) :
    NecklaceCode.Flag.{u} T n ≃ (nerve (OuterPath.{u} T)).obj (op ⦋n⦌) where
  toFun := flagToNerve T
  invFun := nerveToFlag T
  left_inv F := NecklaceCode.Flag.ext (fun _ ↦ rfl)
  right_inv F := CategoryTheory.Functor.ext (fun _ ↦ JointPath.ext rfl)

/-- The whole SSet of unflanked flags equals the nerve of the actual outer joint-path poset. -/
def outerFlagIso : flagSSet.{u} T ≅ nerve (OuterPath.{u} T) :=
  NatIso.ofComponents (fun q ↦ (outerFlagEquiv T q.unop.len).toIso) (by
    intro p q α
    funext F
    exact CategoryTheory.Functor.ext (fun _ ↦ JointPath.ext rfl))

end

end DaggerChosenRigidificationNecklace.NecklaceThickening
