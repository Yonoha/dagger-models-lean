import OriginalProductCrossingSplit

set_option autoImplicit false
open CategoryTheory Limits Opposite Simplicial
open DaggerChosenRigidificationNecklace DaggerChosenRigidificationNecklace.NecklaceCode

universe u

namespace DaggerOriginalProductGadget

noncomputable section

theorem cutLeft_joint (T : NecklaceCode) (j : Fin (T.len + 1)) :
    pointAt (cutLeft T j) (ULift.up (Fin.last _)) ≫ cutLeftι.{u} T j =
      pointAt T (ULift.up j) := by
  rw [pointAt_comp]
  congr 1
  change mapVertices (intervalι T 0 j (Fin.zero_le j)) (ULift.up (Fin.last _)) = _
  rw [intervalι_vertices]
  apply ULift.ext
  exact intervalEmbedding_last T 0 j (Fin.zero_le j)

theorem cutRight_joint (T : NecklaceCode) (j : Fin (T.len + 1)) :
    pointAt (cutRight T j) (ULift.up 0) ≫ cutRightι.{u} T j =
      pointAt T (ULift.up j) := by
  rw [pointAt_comp]
  congr 1
  change mapVertices (intervalι T j (Fin.last T.len) (Fin.le_last j)) (ULift.up 0) = _
  rw [intervalι_vertices]
  apply ULift.ext
  exact intervalEmbedding_first T j (Fin.last T.len) (Fin.le_last j)

theorem productCutLeft_joint (K : SSet.{u}) (T : NecklaceCode) (j : Fin (T.len + 1)) :
    prod.map (𝟙 K) (pointAt (cutLeft T j) (ULift.up (Fin.last _))) ≫
      prod.map (𝟙 K) (cutLeftι T j) = productJointInclusion K T j := by
  rw [prod.map_map, Category.id_comp, cutLeft_joint]
  rfl

theorem productCutRight_joint (K : SSet.{u}) (T : NecklaceCode) (j : Fin (T.len + 1)) :
    prod.map (𝟙 K) (pointAt (cutRight T j) (ULift.up 0)) ≫
      prod.map (𝟙 K) (cutRightι T j) = productJointInclusion K T j := by
  rw [prod.map_map, Category.id_comp, cutRight_joint]
  rfl

variable (K : SSet.{u}) (T S : NecklaceCode) (f : S.toSSet ⟶ K ⨯ T.toSSet)
  (k : Fin (S.len + 1)) (j : Fin (T.len + 1))
  (hk : orderMap (f ≫ prod.snd) k = j)

/-- The left factor ends at the specified point in the actual common product. -/
theorem productCrossingLeft_joint :
    pointAt (cutLeft S k) (ULift.up (Fin.last _)) ≫ productCrossingLeftLift K T S f k j hk =
      productCrossingPoint K T S f k ≫
        prod.map (𝟙 K) (pointAt (cutLeft T j) (ULift.up (Fin.last _))) := by
  have : Mono (prod.map (𝟙 K) (cutLeftι T j)) := (productCut_mono K T j).2.2.1
  apply (cancel_mono (prod.map (𝟙 K) (cutLeftι T j))).mp
  rw [Category.assoc, productCrossingLeft_fac, ← Category.assoc, cutLeft_joint,
    Category.assoc, productCutLeft_joint]
  exact (productCrossingPoint_fac K T S f k j hk).symm

/-- The right factor starts at that same specified point in the common product. -/
theorem productCrossingRight_joint :
    pointAt (cutRight S k) (ULift.up 0) ≫ productCrossingRightLift K T S f k j hk =
      productCrossingPoint K T S f k ≫
        prod.map (𝟙 K) (pointAt (cutRight T j) (ULift.up 0)) := by
  have : Mono (prod.map (𝟙 K) (cutRightι T j)) := (productCut_mono K T j).2.2.2
  apply (cancel_mono (prod.map (𝟙 K) (cutRightι T j))).mp
  rw [Category.assoc, productCrossingRight_fac, ← Category.assoc, cutRight_joint,
    Category.assoc, productCutRight_joint]
  exact (productCrossingPoint_fac K T S f k j hk).symm

end

end DaggerOriginalProductGadget
