import OriginalFlagAssembledNormalization
import Mathlib.Order.Fin.Basic

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial

universe u

namespace DaggerOriginalFlagFlankification

noncomputable section

open DaggerChosenRigidificationNecklace NecklaceCode

variable {X : SSet.{u}} {a b : X.obj (op ⦋0⦌)}

/-- The source fold still has the literal original prefix length, before any EZ collapse. -/
theorem sourcePrefix_len (P : NecklacesOver X a b) (k : ℕ)
    (hk : k ≤ beadCount P.code) :
    (orderedPrefix P k hk).source.code.len =
      (jointEmbedding P.code ⟨k, Nat.lt_succ_of_le hk⟩).val := by
  induction k with
  | zero =>
    change 0 = (jointEmbedding P.code 0).val
    rw [jointEmbedding_first]
    rfl
  | succ k ih =>
    let hp : k ≤ beadCount P.code := Nat.le_of_succ_le hk
    let i : Fin (beadCount P.code) := ⟨k, lt_of_lt_of_le (Nat.lt_succ_self k) hk⟩
    have hprev : (⟨k, Nat.lt_succ_of_le hp⟩ : Fin (beadCount P.code + 1)) =
        i.castSucc := Fin.ext rfl
    have hnext : (⟨k + 1, Nat.lt_succ_of_le hk⟩ : Fin (beadCount P.code + 1)) =
        i.succ := Fin.ext rfl
    change (orderedPrefix P k hp).source.code.len + (jointBead P.code i).length = _
    rw [ih hp, hprev, hnext, jointBead_length]
    have hlt := (jointBead P.code i).lt
    change (jointEmbedding P.code i.castSucc).val <
      (jointEmbedding P.code i.succ).val at hlt
    omega

/-- The same original coordinate, not an arbitrary bijection of source object sets. -/
def sourcePrefixEmbedding (P : NecklacesOver X a b) (k : ℕ)
    (hk : k ≤ beadCount P.code) :
    Fin ((orderedPrefix P k hk).source.code.len + 1) ↪o Fin (P.code.len + 1) where
  toFun v := ⟨v.val, by
    have hv := v.isLt
    have hc := (jointEmbedding P.code ⟨k, Nat.lt_succ_of_le hk⟩).isLt
    have he := sourcePrefix_len P k hk
    omega⟩
  inj' v w h := Fin.ext (congrArg (fun z : Fin (P.code.len + 1) ↦ z.val) h)
  map_rel_iff' := by intro v w; rfl

theorem sourcePrefixEmbedding_val (P : NecklacesOver X a b) (k : ℕ)
    (hk : k ≤ beadCount P.code)
    (v : Fin ((orderedPrefix P k hk).source.code.len + 1)) :
    (sourcePrefixEmbedding P k hk v).val = v.val := rfl

theorem sourcePrefixEmbedding_first (P : NecklacesOver X a b) (k : ℕ)
    (hk : k ≤ beadCount P.code) : sourcePrefixEmbedding P k hk 0 = 0 := Fin.ext rfl

theorem sourcePrefixEmbedding_last (P : NecklacesOver X a b) (k : ℕ)
    (hk : k ≤ beadCount P.code) :
    sourcePrefixEmbedding P k hk (Fin.last (orderedPrefix P k hk).source.code.len) =
      jointEmbedding P.code ⟨k, Nat.lt_succ_of_le hk⟩ :=
  Fin.ext (sourcePrefix_len P k hk)

theorem assembledSource_len (P : NecklacesOver X a b) :
    (assembledSource P).code.len = P.code.len := by
  have h := sourcePrefix_len P (beadCount P.code) le_rfl
  have hl : (⟨beadCount P.code, Nat.lt_succ_self _⟩ :
      Fin (beadCount P.code + 1)) = Fin.last (beadCount P.code) := Fin.ext rfl
  have hj := congrArg
    (fun j : Fin (beadCount P.code + 1) ↦ (jointEmbedding P.code j).val) hl
  have he := congrArg (fun v : Fin (P.code.len + 1) ↦ v.val)
    (jointEmbedding_last P.code)
  exact h.trans (hj.trans he)

/-- Both vertex inverse laws use the existing Fin.cast order isomorphism. -/
def sourceAssemblyOrderIso (P : NecklacesOver X a b) :
    Fin ((assembledSource P).code.len + 1) ≃o Fin (P.code.len + 1) :=
  Fin.castOrderIso (congrArg (fun n : ℕ ↦ n + 1) (assembledSource_len P))

theorem sourceAssemblyOrderIso_val (P : NecklacesOver X a b)
    (v : Fin ((assembledSource P).code.len + 1)) :
    (sourceAssemblyOrderIso P v).val = v.val := rfl

theorem sourceAssemblyOrderIso_first (P : NecklacesOver X a b) :
    sourceAssemblyOrderIso P 0 = 0 := Fin.ext rfl

theorem sourceAssemblyOrderIso_last (P : NecklacesOver X a b) :
    sourceAssemblyOrderIso P (Fin.last (assembledSource P).code.len) =
      Fin.last P.code.len := Fin.ext (assembledSource_len P)

end

end DaggerOriginalFlagFlankification
