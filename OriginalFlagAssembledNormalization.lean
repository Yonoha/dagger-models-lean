import OriginalFlagPrefixNormalization

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial

universe u

namespace DaggerOriginalFlagFlankification

noncomputable section

open DaggerChosenRigidificationNecklace NecklaceCode

variable {X : SSet.{u}} {a b : X.obj (op ⦋0⦌)}

/-- Only endpoints are reindexed; the complete source-prefix code and map remain unchanged. -/
def assembledSource (P : NecklacesOver X a b) : NecklacesOver X a b where
  code := (orderedPrefix P (beadCount P.code) le_rfl).source.code
  map := (orderedPrefix P (beadCount P.code) le_rfl).source.map
  first := (orderedPrefix P (beadCount P.code) le_rfl).source.first.trans
    (jointVertex_first P)
  last := (orderedPrefix P (beadCount P.code) le_rfl).source.last.trans
    (jointVertex_last P)

/-- The exact finite normalized map, retaining every image simplex and the original endpoints. -/
def normOver (P : NecklacesOver X a b) : NecklacesOver X a b where
  code := (orderedPrefix P (beadCount P.code) le_rfl).normalized.code
  map := (orderedPrefix P (beadCount P.code) le_rfl).normalized.map
  first := (orderedPrefix P (beadCount P.code) le_rfl).normalized.first.trans
    (jointVertex_first P)
  last := (orderedPrefix P (beadCount P.code) le_rfl).normalized.last.trans
    (jointVertex_last P)

/-- This is the finite assembly arrow; its source has not yet been identified with P here. -/
def assembledNormalization (P : NecklacesOver X a b) : assembledSource P ⟶ normOver P where
  hom := (orderedPrefix P (beadCount P.code) le_rfl).ν.hom
  w := (orderedPrefix P (beadCount P.code) le_rfl).ν.w

theorem assembledNormalization_triangle (P : NecklacesOver X a b) :
    (assembledNormalization P).hom.map ≫ (normOver P).map = (assembledSource P).map :=
  (assembledNormalization P).w

theorem assembledNormalization_surjective (P : NecklacesOver X a b) :
    Function.Surjective (mapVertices (assembledNormalization P).hom.map) :=
  orderedPrefix_surjective P _ _

theorem orderedPrefix_zero_dims (P : NecklacesOver X a b) (k : ℕ)
    (hk : k ≤ beadCount P.code)
    (hz : ∀ i : Fin (beadCount P.code), (normalizeBead P (jointBead P.code i)).dim = 0) :
    (orderedPrefix P k hk).normalized.code.len = 0 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change (orderedPrefix P k (Nat.le_of_succ_le hk)).normalized.code.len +
      (normalizeBead P (jointBead P.code
        ⟨k, lt_of_lt_of_le (Nat.lt_succ_self k) hk⟩)).dim = 0
    rw [ih, hz]

theorem code_zero_eq_point (T : NecklaceCode) (h : T.len = 0) : T = NecklaceCode.point := by
  cases T with
  | mk len joints first last =>
    dsimp at h
    subst len
    have hj : joints = {0} := by
      ext v
      have hv : v = 0 := by
        apply Fin.ext
        have hv := v.isLt
        change v.val < 1 at hv
        omega
      simp [hv, first]
    cases hj
    rfl

theorem normOver_all_zero_code (P : NecklacesOver X a b)
    (hz : ∀ i : Fin (beadCount P.code), (normalizeBead P (jointBead P.code i)).dim = 0) :
    (normOver P).code = NecklaceCode.point :=
  code_zero_eq_point _ (orderedPrefix_zero_dims P _ _ hz)

theorem normOver_all_zero_endpoints (P : NecklacesOver X a b)
    (hz : ∀ i : Fin (beadCount P.code), (normalizeBead P (jointBead P.code i)).dim = 0) :
    a = b := by
  have hc := normOver_all_zero_code P hz
  have hends : (normOver P).code.first = (normOver P).code.last := by
    rw [hc]
    rfl
  exact (normOver P).first.symm.trans
    ((congrArg ((normOver P).map.app (op ⦋0⦌)) hends).trans (normOver P).last)

end

end DaggerOriginalFlagFlankification
