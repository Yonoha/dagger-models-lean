import OriginalFlagSourcePrefixCoordinates

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial

universe u

namespace DaggerOriginalFlagFlankification

noncomputable section

open DaggerChosenRigidificationNecklace NecklaceCode

variable {X : SSet.{u}} {a b : X.obj (op ⦋0⦌)}

/-- The source fold contains precisely the original joints in the same prefix coordinates. -/
theorem sourcePrefix_joint_iff (P : NecklacesOver X a b) (k : ℕ)
    (hk : k ≤ beadCount P.code)
    (v : Fin ((orderedPrefix P k hk).source.code.len + 1)) :
    v ∈ (orderedPrefix P k hk).source.code.joints ↔
      sourcePrefixEmbedding P k hk v ∈ P.code.joints := by
  induction k with
  | zero =>
    have hv : v = 0 := by
      apply Fin.ext
      change v.val = 0
      have h := v.isLt
      change v.val < 1 at h
      omega
    subst v
    rw [sourcePrefixEmbedding_first]
    exact iff_of_true (by simp [orderedPrefix, NecklacesOver.point, NecklaceCode.point])
      P.code.first_mem
  | succ k ih =>
    let hp : k ≤ beadCount P.code := Nat.le_of_succ_le hk
    let i : Fin (beadCount P.code) := ⟨k, lt_of_lt_of_le (Nat.lt_succ_self k) hk⟩
    let c := jointBead P.code i
    let T := (orderedPrefix P k hp).source.code
    have hT : T.len = c.left.val := by
      have h := sourcePrefix_len P k hp
      change T.len = (jointEmbedding P.code ⟨k, Nat.lt_succ_of_le hp⟩).val at h
      convert h using 1
    have hN : T.len + c.length = c.right.val := by
      have h := sourcePrefix_len P (k + 1) hk
      change T.len + c.length =
        (jointEmbedding P.code ⟨k + 1, Nat.lt_succ_of_le hk⟩).val at h
      convert h using 1
    change v ∈ (wedge T (single c.length)).joints ↔
      sourcePrefixEmbedding P (k + 1) hk v ∈ P.code.joints
    constructor
    · intro hv
      rcases Finset.mem_union.mp hv with hv | hv
      · obtain ⟨w, hw, he⟩ := Finset.mem_image.mp hv
        have hj := (ih hp w).mp hw
        have hmap : sourcePrefixEmbedding P k hp w =
            sourcePrefixEmbedding P (k + 1) hk v := by
          apply Fin.ext
          change w.val = v.val
          exact congrArg (fun z : Fin ((wedge T (single c.length)).len + 1) ↦ z.val) he
        exact hmap ▸ hj
      · obtain ⟨w, hw, he⟩ := Finset.mem_image.mp hv
        rcases (mem_single_joints c.length w).mp hw with hw | hw
        · subst w
          have hmap : sourcePrefixEmbedding P (k + 1) hk v = c.left := by
            apply Fin.ext
            change v.val = c.left.val
            have h := congrArg Fin.val he
            change T.len + 0 = v.val at h
            omega
          exact hmap.symm ▸ c.left_mem
        · subst w
          have hmap : sourcePrefixEmbedding P (k + 1) hk v = c.right := by
            apply Fin.ext
            change v.val = c.right.val
            have h := congrArg Fin.val he
            change T.len + c.length = v.val at h
            omega
          exact hmap.symm ▸ c.right_mem
    · intro hv
      by_cases hpre : v.val ≤ T.len
      · let w : Fin (T.len + 1) := ⟨v.val, by omega⟩
        have hmap : sourcePrefixEmbedding P k hp w =
            sourcePrefixEmbedding P (k + 1) hk v := Fin.ext rfl
        have hw : w ∈ T.joints := (ih hp w).mpr (hmap.symm ▸ hv)
        apply Finset.mem_union_left
        exact Finset.mem_image.mpr ⟨w, hw, Fin.ext rfl⟩
      · have hl : c.left < sourcePrefixEmbedding P (k + 1) hk v := by
          change c.left.val < v.val
          omega
        have hr : sourcePrefixEmbedding P (k + 1) hk v ≤ c.right := by
          change v.val ≤ c.right.val
          have h := v.isLt
          change v.val < T.len + c.length + 1 at h
          omega
        have he : sourcePrefixEmbedding P (k + 1) hk v = c.right :=
          le_antisymm hr (le_of_not_gt (fun h ↦ c.no_joint _ hv hl h))
        apply Finset.mem_union_right
        refine Finset.mem_image.mpr ⟨Fin.last c.length, (single c.length).last_mem, ?_⟩
        apply Fin.ext
        have h := congrArg Fin.val he
        change v.val = c.right.val at h
        change T.len + c.length = v.val
        omega

theorem sourceAssembly_joint_iff (P : NecklacesOver X a b)
    (v : Fin ((assembledSource P).code.len + 1)) :
    v ∈ (assembledSource P).code.joints ↔ sourceAssemblyOrderIso P v ∈ P.code.joints := by
  have hmap : sourcePrefixEmbedding P (beadCount P.code) le_rfl v =
      sourceAssemblyOrderIso P v := Fin.ext rfl
  rw [← hmap]
  exact sourcePrefix_joint_iff P _ _ v

theorem sourceAssembly_inverse_joint_iff (P : NecklacesOver X a b)
    (v : Fin (P.code.len + 1)) :
    (sourceAssemblyOrderIso P).symm v ∈ (assembledSource P).code.joints ↔
      v ∈ P.code.joints := by
  rw [sourceAssembly_joint_iff, OrderIso.apply_symm_apply]

/-- Both images, including the initial point joint, are retained literally. -/
theorem sourceAssembly_joint_image (P : NecklacesOver X a b) :
    sourceAssemblyOrderIso P '' {v | v ∈ (assembledSource P).code.joints} =
      {v | v ∈ P.code.joints} := by
  ext v
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact (sourceAssembly_joint_iff P w).mp hw
  · intro hv
    exact ⟨(sourceAssemblyOrderIso P).symm v,
      (sourceAssembly_inverse_joint_iff P v).mpr hv, (sourceAssemblyOrderIso P).apply_symm_apply v⟩

end

end DaggerOriginalFlagFlankification
