import ChosenNecklaceIntervalMaps
import ChosenNecklaceClippedBeads

open CategoryTheory Limits Opposite Simplicial

universe u

namespace DaggerChosenRigidificationNecklace.NecklaceCode

noncomputable section

variable (T : NecklaceCode) (a b : Fin (T.len + 1)) (hab : a ≤ b) {n : ℕ}

def intervalPreSimplex (x : (toSSet.{u} T).obj (op ⦋n⦌))
    (hx : ∀ i, a ≤ T.inclusion.app _ x i ∧ T.inclusion.app _ x i ≤ b) :
    (Δ[(intervalCode T a b hab).len] : SSet.{u}).obj (op ⦋n⦌) :=
  SSet.stdSimplex.objMk
    ⟨fun i ↦ ⟨(T.inclusion.app _ x i).val - a.val, by
      have h : (T.inclusion.app _ x i).val ≤ b.val := (hx i).2
      change (T.inclusion.app _ x i).val - a.val < b.val - a.val + 1
      omega⟩,
      fun _ _ h ↦ Nat.sub_le_sub_right
        (show (T.inclusion.app _ x _).val ≤ (T.inclusion.app _ x _).val from
          SSet.stdSimplex.monotone_apply _ h) a.val⟩

theorem intervalPreSimplex_embedding (x : (toSSet.{u} T).obj (op ⦋n⦌))
    (hx : ∀ i, a ≤ T.inclusion.app _ x i ∧ T.inclusion.app _ x i ≤ b) (i : Fin (n + 1)) :
    intervalEmbedding T a b hab (intervalPreSimplex T a b hab x hx i) =
      T.inclusion.app _ x i := by
  apply Fin.ext
  change a.val + ((T.inclusion.app _ x i).val - a.val) = (T.inclusion.app _ x i).val
  have h : a.val ≤ (T.inclusion.app _ x i).val := (hx i).1
  omega

theorem intervalPreSimplex_mem (x : (toSSet.{u} T).obj (op ⦋n⦌))
    (hx : ∀ i, a ≤ T.inclusion.app _ x i ∧ T.inclusion.app _ x i ≤ b) :
    intervalPreSimplex T a b hab x hx ∈ (intervalCode T a b hab).complex.obj (op ⦋n⦌) := by
  have hm := (T.complexIso.hom.app _ x).property
  rcases (T.mem_complex_iff _).mp hm with h | ⟨d, h⟩
  · apply ((intervalCode T a b hab).mem_complex_iff _).mpr
    left
    intro i
    apply Fin.ext
    change (T.inclusion.app _ x i).val - a.val = 0
    have hi := congrArg Fin.val (h i)
    change (T.inclusion.app _ x i).val = 0 at hi
    omega
  · by_cases hd : max a d.left < min b d.right
    · apply ((intervalCode T a b hab).mem_complex_iff _).mpr
      right
      refine ⟨clippedBead T a b hab d hd, fun i ↦ ?_⟩
      apply clippedBead_preimage
      rw [intervalPreSimplex_embedding]
      exact h i
    · apply constant_mem_complex (intervalCode T a b hab)
        (intervalPreSimplex T a b hab x hx 0)
      intro i
      have hi : max a d.left ≤ T.inclusion.app _ x i ∧
          T.inclusion.app _ x i ≤ min b d.right := by
        obtain ⟨hl, hr⟩ := Finset.mem_Icc.mp (h i)
        exact ⟨max_le (hx i).1 hl, le_min (hx i).2 hr⟩
      have h0 : max a d.left ≤ T.inclusion.app _ x 0 ∧
          T.inclusion.app _ x 0 ≤ min b d.right := by
        obtain ⟨hl, hr⟩ := Finset.mem_Icc.mp (h 0)
        exact ⟨max_le (hx 0).1 hl, le_min (hx 0).2 hr⟩
      have he : T.inclusion.app _ x i = T.inclusion.app _ x 0 :=
        le_antisymm (hi.2.trans ((le_of_not_gt hd).trans h0.1))
          (h0.2.trans ((le_of_not_gt hd).trans hi.1))
      apply Fin.ext
      change (T.inclusion.app _ x i).val - a.val = (T.inclusion.app _ x 0).val - a.val
      rw [he]

def intervalLiftSimplex (x : (toSSet.{u} T).obj (op ⦋n⦌))
    (hx : ∀ i, a ≤ T.inclusion.app _ x i ∧ T.inclusion.app _ x i ≤ b) :
    (toSSet.{u} (intervalCode T a b hab)).obj (op ⦋n⦌) :=
  (intervalCode T a b hab).complexIso.inv.app _
    ⟨intervalPreSimplex T a b hab x hx, intervalPreSimplex_mem T a b hab x hx⟩

theorem intervalLiftSimplex_inclusion (x : (toSSet.{u} T).obj (op ⦋n⦌))
    (hx : ∀ i, a ≤ T.inclusion.app _ x i ∧ T.inclusion.app _ x i ≤ b) :
    (intervalCode T a b hab).inclusion.app _ (intervalLiftSimplex T a b hab x hx) =
      intervalPreSimplex T a b hab x hx := by
  have h := congrFun (NatTrans.congr_app (intervalCode T a b hab).complexIso.inv_hom_id
    (op ⦋n⦌)) ⟨intervalPreSimplex T a b hab x hx, intervalPreSimplex_mem T a b hab x hx⟩
  exact congrArg Subtype.val h

theorem intervalι_apply (x : (toSSet.{u} (intervalCode T a b hab)).obj (op ⦋n⦌))
    (i : Fin (n + 1)) : T.inclusion.app _ ((intervalι T a b hab).app _ x) i =
      intervalEmbedding T a b hab ((intervalCode T a b hab).inclusion.app _ x i) := by
  have h := congrFun (NatTrans.congr_app (intervalι_inclusion.{u} T a b hab) (op ⦋n⦌)) x
  exact congrArg (fun y : (Δ[T.len] : SSet.{u}).obj (op ⦋n⦌) ↦ y i) h

theorem intervalι_lift (x : (toSSet.{u} T).obj (op ⦋n⦌))
    (hx : ∀ i, a ≤ T.inclusion.app _ x i ∧ T.inclusion.app _ x i ≤ b) :
    (intervalι T a b hab).app _ (intervalLiftSimplex T a b hab x hx) = x := by
  apply necklace_simplex_ext T
  intro i
  rw [intervalι_apply, intervalLiftSimplex_inclusion, intervalPreSimplex_embedding]

end

end DaggerChosenRigidificationNecklace.NecklaceCode
