import OriginalCrossingArrowLift

set_option autoImplicit false
open CategoryTheory Limits Opposite Simplicial
open DaggerChosenRigidificationNecklace
open DaggerChosenRigidificationNecklace.NecklaceCode

universe u

namespace DaggerOriginalProductGadget

noncomputable section

theorem intervalPoint_first (S : NecklaceCode) (k l : Fin (S.len + 1)) (hkl : k ≤ l) :
    pointAt (intervalCode S k l hkl) (ULift.up 0) ≫ intervalι.{u} S k l hkl =
      pointAt S (ULift.up k) := by
  rw [pointAt_comp, intervalι_vertices, intervalEmbedding_first]

theorem intervalPoint_last (S : NecklaceCode) (k l : Fin (S.len + 1)) (hkl : k ≤ l) :
    pointAt (intervalCode S k l hkl) (ULift.up (Fin.last _)) ≫ intervalι.{u} S k l hkl =
      pointAt S (ULift.up l) := by
  rw [pointAt_comp, intervalι_vertices]
  congr 1
  exact ULift.ext _ _ (intervalEmbedding_last S k l hkl)

instance productJointInclusion_mono (K : SSet.{u}) (T : NecklaceCode)
    (j : Fin (T.len + 1)) : Mono (productJointInclusion K T j) := by
  have : Mono (pointAt T (ULift.up j)) := SSet.stdSimplex.isTerminalObj₀.mono_from _
  change Mono (prod.map (𝟙 K) (pointAt T (ULift.up j)))
  infer_instance

variable (K : SSet.{u}) (T S : NecklaceCode) (f : S.toSSet ⟶ K ⨯ T.toSSet)
  (k l : Fin (S.len + 1)) (hkl : k ≤ l) (j : Fin (T.len + 1))
  (hk : orderMap (f ≫ prod.snd) k = j) (hl : orderMap (f ≫ prod.snd) l = j)

include hk hl in
/-- The actual interval between any two cuts over the same interface lifts into that interface,
with both supplied endpoint maps retained. Joint membership is not needed for this factorization. -/
theorem productPlateau_exists :
    ∃ m : (intervalCode S k l hkl).toSSet ⟶ K ⨯ (Δ[0] : SSet.{u}),
      m ≫ productJointInclusion K T j = intervalι S k l hkl ≫ f ∧
      pointAt (intervalCode S k l hkl) (ULift.up 0) ≫ m = productCrossingPoint K T S f k ∧
      pointAt (intervalCode S k l hkl) (ULift.up (Fin.last _)) ≫ m =
        productCrossingPoint K T S f l := by
  apply productPointAt_necklaceSimple K T (ULift.up j) (intervalCode S k l hkl)
    (productCrossingPoint K T S f k) (productCrossingPoint K T S f l)
    (intervalι S k l hkl ≫ f)
  · rw [← Category.assoc, intervalPoint_first]
    exact (productCrossingPoint_fac K T S f k j hk).symm
  · rw [← Category.assoc, intervalPoint_last]
    exact (productCrossingPoint_fac K T S f l j hl).symm

/-- A lift through the original common-product inclusion.
Uniqueness below removes dependence on the choice of lift. -/
def productPlateauLift : (intervalCode S k l hkl).toSSet ⟶ K ⨯ (Δ[0] : SSet.{u}) :=
  Classical.choose (productPlateau_exists K T S f k l hkl j hk hl)

theorem productPlateauLift_fac :
    productPlateauLift K T S f k l hkl j hk hl ≫ productJointInclusion K T j =
      intervalι S k l hkl ≫ f :=
  (Classical.choose_spec (productPlateau_exists K T S f k l hkl j hk hl)).1

theorem productPlateauLift_first :
    pointAt (intervalCode S k l hkl) (ULift.up 0) ≫
        productPlateauLift K T S f k l hkl j hk hl = productCrossingPoint K T S f k :=
  (Classical.choose_spec (productPlateau_exists K T S f k l hkl j hk hl)).2.1

theorem productPlateauLift_last :
    pointAt (intervalCode S k l hkl) (ULift.up (Fin.last _)) ≫
        productPlateauLift K T S f k l hkl j hk hl = productCrossingPoint K T S f l :=
  (Classical.choose_spec (productPlateau_exists K T S f k l hkl j hk hl)).2.2

theorem productPlateauLift_unique
    (m : (intervalCode S k l hkl).toSSet ⟶ K ⨯ (Δ[0] : SSet.{u}))
    (hm : m ≫ productJointInclusion K T j = intervalι S k l hkl ≫ f) :
    m = productPlateauLift K T S f k l hkl j hk hl := by
  apply (cancel_mono (productJointInclusion K T j)).mp
  exact hm.trans (productPlateauLift_fac K T S f k l hkl j hk hl).symm

end

end DaggerOriginalProductGadget
