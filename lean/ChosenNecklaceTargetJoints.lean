import ChosenNecklaceIntervalTerminal

open CategoryTheory Limits Opposite Simplicial

universe u

namespace DaggerChosenRigidificationNecklace

noncomputable section

open NecklaceCode

namespace NecklaceCode

theorem orderMap_comp_apply {T U V : NecklaceCode}
    (f : toSSet.{u} T ⟶ toSSet.{u} U) (g : toSSet.{u} U ⟶ toSSet.{u} V)
    (v : Fin (T.len + 1)) : orderMap (f ≫ g) v = orderMap g (orderMap f v) := by
  dsimp [orderMap, mapVertices]
  rw [U.verticesEquiv.symm_apply_apply]

end NecklaceCode

variable (T : NecklaceCode) (a b : Fin (T.len + 1))
  (P : NecklacesOver (toSSet.{u} T)
    (T.verticesEquiv.symm (ULift.up a)) (T.verticesEquiv.symm (ULift.up b)))

/-- Every original target joint between the supplied endpoints is the image of a source joint. -/
theorem over_target_joint (j : Fin (T.len + 1)) (hj : j ∈ T.joints)
    (ha : a ≤ j) (hb : j ≤ b) : ∃ k ∈ P.code.joints, orderMap P.map k = j := by
  let hab := over_endpoints_le T a b P
  obtain ⟨l, hl⟩ := intervalEmbedding_preimage T a b hab j ha hb
  have hlJ : l ∈ (intervalCode T a b hab).joints :=
    (intervalCode_joint T a b hab l).mpr (Or.inr (Or.inr (hl.symm ▸ hj)))
  obtain ⟨k, hk, he⟩ := Finset.mem_image.mp
    (joints_subset_image (toInterval T a b hab P).hom hlJ)
  refine ⟨k, hk, ?_⟩
  rw [← toInterval_original T a b hab P, orderMap_comp_apply, he]
  change (mapVertices (intervalι T a b hab) (ULift.up l)).down = j
  rw [intervalι_vertices]
  exact hl

variable {T : NecklaceCode} {x y : (toSSet.{u} T).obj (op ⦋0⦌)}

/-- Reindex only the two endpoint equalities; the entire original over-map stays the same. -/
def overAtCoordinates (P : NecklacesOver (toSSet.{u} T) x y) :
    NecklacesOver (toSSet.{u} T)
      (T.verticesEquiv.symm (ULift.up (T.verticesEquiv x).down))
      (T.verticesEquiv.symm (ULift.up (T.verticesEquiv y).down)) where
  code := P.code
  map := P.map
  first := P.first.trans (T.verticesEquiv.symm_apply_apply x).symm
  last := P.last.trans (T.verticesEquiv.symm_apply_apply y).symm

theorem original_over_target_joint (P : NecklacesOver (toSSet.{u} T) x y)
    (j : Fin (T.len + 1)) (hj : j ∈ T.joints)
    (hx : (T.verticesEquiv x).down ≤ j) (hy : j ≤ (T.verticesEquiv y).down) :
    ∃ k ∈ P.code.joints, orderMap P.map k = j :=
  over_target_joint T _ _ (overAtCoordinates P) j hj hx hy

end

end DaggerChosenRigidificationNecklace
