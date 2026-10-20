import OriginalProductPlateau
import ChosenFlagHomMaps

set_option autoImplicit false
open CategoryTheory Limits Opposite Simplicial
open DaggerChosenRigidificationNecklace
open DaggerChosenRigidificationNecklace.NecklaceCode

universe u

namespace DaggerOriginalProductGadget

noncomputable section

theorem productCrossingPoint_vertex (K : SSet.{u}) (T S : NecklaceCode)
    (f : S.toSSet ⟶ K ⨯ T.toSSet) (k : Fin (S.len + 1)) (j : Fin (T.len + 1))
    (hk : orderMap (f ≫ prod.snd) k = j) :
    (productJointInclusion K T j).app _ (SSet.yonedaEquiv (productCrossingPoint K T S f k)) =
      f.app _ (S.verticesEquiv.symm (ULift.up k)) := by
  have h := congrArg SSet.yonedaEquiv (productCrossingPoint_fac K T S f k j hk)
  simpa only [SSet.yonedaEquiv_comp, pointAt_vertex] using h

variable (K : SSet.{u}) (T S : NecklaceCode) (f : S.toSSet ⟶ K ⨯ T.toSSet)
  (k l : Fin (S.len + 1)) (hkl : k ≤ l) (j : Fin (T.len + 1))
  (hk : orderMap (f ≫ prod.snd) k = j) (hl : orderMap (f ≫ prod.snd) l = j)

/-- The actual middle necklace over the common product, with both specified crossing endpoints. -/
def productPlateauOver : NecklacesOver (K ⨯ (Δ[0] : SSet.{u}))
    (SSet.yonedaEquiv (productCrossingPoint K T S f k))
    (SSet.yonedaEquiv (productCrossingPoint K T S f l)) where
  code := intervalCode S k l hkl
  map := productPlateauLift K T S f k l hkl j hk hl
  first := by
    have h := congrArg SSet.yonedaEquiv (productPlateauLift_first K T S f k l hkl j hk hl)
    simpa only [SSet.yonedaEquiv_comp, pointAt_vertex, first] using h
  last := by
    have h := congrArg SSet.yonedaEquiv (productPlateauLift_last K T S f k l hkl j hk hl)
    simpa only [SSet.yonedaEquiv_comp, pointAt_vertex, last] using h

/-- The same literal interval map into the total product; its endpoints are the images
of the specified common-product points, identified by productCrossingPoint_vertex. -/
def productPlateauImageOver : NecklacesOver (K ⨯ T.toSSet)
    ((productJointInclusion K T j).app _
      (SSet.yonedaEquiv (productCrossingPoint K T S f k)))
    ((productJointInclusion K T j).app _
      (SSet.yonedaEquiv (productCrossingPoint K T S f l))) where
  code := intervalCode S k l hkl
  map := intervalι S k l hkl ≫ f
  first := by
    change f.app _ ((intervalι S k l hkl).app _ (intervalCode S k l hkl).first) = _
    rw [intervalι_first]
    exact (productCrossingPoint_vertex K T S f k j hk).symm
  last := by
    change f.app _ ((intervalι S k l hkl).app _ (intervalCode S k l hkl).last) = _
    rw [intervalι_last]
    exact (productCrossingPoint_vertex K T S f l j hl).symm

/-- Identity on the middle necklace code gives an original over-product comparison arrow. -/
def productPlateauImageHom : NecklacesOver.Hom
    ((NecklacesOver.postcomp (productJointInclusion K T j)).obj
      (productPlateauOver K T S f k l hkl j hk hl))
    (productPlateauImageOver K T S f k l hkl j hk hl) where
  hom := NecklaceCode.Hom.id _
  w := by
    change 𝟙 _ ≫ (intervalι S k l hkl ≫ f) =
      productPlateauLift K T S f k l hkl j hk hl ≫ productJointInclusion K T j
    rw [Category.id_comp]
    exact (productPlateauLift_fac K T S f k l hkl j hk hl).symm

/-- Every supplied middle flag is the actual image of a flag in the common-product Hom. -/
theorem productPlateauFlag_image {n : ℕ}
    (M : Flag.{u} (intervalCode S k l hkl) n) :
    (flagHomMap (productJointInclusion K T j)).app (op ⦋n⦌)
        (Quot.mk _ (⟨productPlateauOver K T S f k l hkl j hk hl, M⟩ :
          RawFlag _ _ _ (op ⦋n⦌))) =
      Quot.mk _ (⟨productPlateauImageOver K T S f k l hkl j hk hl, M⟩ :
        RawFlag _ _ _ (op ⦋n⦌)) := by
  exact Quot.sound ⟨productPlateauImageHom K T S f k l hkl j hk hl,
    (NecklaceCode.Flag.map_id M).symm⟩

end

end DaggerOriginalProductGadget
