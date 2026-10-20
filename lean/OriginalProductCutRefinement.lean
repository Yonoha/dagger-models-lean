import OriginalIntervalFlagRefinement
import OriginalProductPlateauFlag

set_option autoImplicit false
open CategoryTheory Limits Opposite Simplicial
open DaggerChosenRigidificationNecklace
open DaggerChosenRigidificationNecklace.NecklaceCode

universe u

namespace DaggerOriginalProductGadget

noncomputable section

/-- Two specified cuts of the same original flag over the same interface have one
common triple refinement. Its middle flag is the literal image of a flag in the
common-product Hom, with the exact crossing endpoints retained. -/
theorem productFlag_cut_refinement (K : SSet.{u}) (T S : NecklaceCode)
    (f : S.toSSet ⟶ K ⨯ T.toSSet) (k l : Fin (S.len + 1)) (hkl : k ≤ l)
    (hkJ : k ∈ S.joints) (hlJ : l ∈ S.joints) (j : Fin (T.len + 1))
    (hk : orderMap (f ≫ prod.snd) k = j) (hl : orderMap (f ≫ prod.snd) l = j)
    {n : ℕ} (H : Flag.{u} S n) :
    ∃ (F : Flag.{u} (cutLeft S k) n)
      (M : Flag.{u} (intervalCode S k l hkl) n) (G : Flag.{u} (cutRight S l) n),
      (cutFlagIso S k hkJ).hom.app (op ⦋n⦌) H =
        (F, (intervalFlagCompose S k l (Fin.last S.len) hkl (Fin.le_last l)).app
          (op ⦋n⦌) (M, G)) ∧
      (cutFlagIso S l hlJ).hom.app (op ⦋n⦌) H =
        ((intervalFlagCompose S 0 k l (Fin.zero_le k) hkl).app (op ⦋n⦌) (F, M), G) ∧
      (flagHomMap (productJointInclusion K T j)).app (op ⦋n⦌)
          (Quot.mk _ (⟨productPlateauOver K T S f k l hkl j hk hl, M⟩ :
            RawFlag _ _ _ (op ⦋n⦌))) =
        Quot.mk _ (⟨productPlateauImageOver K T S f k l hkl j hk hl, M⟩ :
          RawFlag _ _ _ (op ⦋n⦌)) := by
  obtain ⟨F, M, G, hF, hG⟩ := fullFlag_common_refinement S k l hkl hkJ hlJ H
  exact ⟨F, M, G, hF, hG, productPlateauFlag_image K T S f k l hkl j hk hl M⟩

end

end DaggerOriginalProductGadget
