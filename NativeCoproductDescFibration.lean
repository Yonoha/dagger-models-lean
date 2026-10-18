import NativeCoproductMapFibration

/-! Coproduct descent to a common base preserves Kan fibrations by connected horn lifting. -/
set_option autoImplicit false
open CategoryTheory Limits Simplicial Opposite HomotopicalAlgebra
open DaggerNativeCoproductConnectedFactor DaggerNativeSSetCoproductSummandFibration
open DaggerOriginalSimplicialCategoryBarCoproductDegrees
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerNativeCoproductDescFibration
noncomputable section

theorem sigma_desc_horn_lifting {I : Type u} {X : I → SSet.{u}} {B : SSet.{u}}
    (f : ∀ i, X i ⟶ B) [∀ i, Fibration (f i)] (n : ℕ) (k : Fin (n + 2)) :
    HasLiftingProperty (SSet.horn (n + 1) k).ι (Limits.Sigma.desc f) where
  sq_hasLift := by
    intro a b sq
    obtain ⟨v⟩ := hornVertex_nonempty n k
    obtain ⟨⟨i, t⟩, ht⟩ := (coproductDegreeEquiv X (op ⦋0⦌)).surjective
      (a.app (op ⦋0⦌) v)
    obtain ⟨g, hg⟩ := connected_factor_fixed_summand X i a v t ht.symm
    have hsq : CommSq g (SSet.horn (n + 1) k).ι (f i) b := ⟨by
      rw [← Limits.Sigma.ι_desc f i, ← Category.assoc, hg]
      exact sq.w⟩
    have ht : trivialCofibrations SSet.{u} (SSet.horn (n + 1) k).ι :=
      (DaggerOrdinaryAnodyneTensor.anodyne_iff_trivialCofibration _).mp
        (SSet.anodyneExtensions.horn_ι_mem n k)
    have : HasLiftingProperty (SSet.horn (n + 1) k).ι (f i) :=
      (show (trivialCofibrations SSet.{u}).rlp (f i) from
        (by rw [trivialCofibrations_rlp]; exact (fibration_iff _).mp inferInstance))
        _ ht
    have : hsq.HasLift := inferInstance
    refine CommSq.HasLift.mk' ⟨hsq.lift ≫ Limits.Sigma.ι X i, ?_, ?_⟩
    · rw [← Category.assoc, hsq.fac_left, hg]
    · rw [Category.assoc, Limits.Sigma.ι_desc, hsq.fac_right]

theorem sigma_desc_fibration {I : Type u} {X : I → SSet.{u}} {B : SSet.{u}}
    (f : ∀ i, X i ⟶ B) [∀ i, Fibration (f i)] :
    Fibration (Limits.Sigma.desc f) := by
  rw [SSet.modelCategoryQuillen.fibration_iff]
  intro P Q j hj
  simp only [SSet.modelCategoryQuillen.J, MorphismProperty.iSup_iff] at hj
  obtain ⟨n, ⟨k⟩⟩ := hj
  exact sigma_desc_horn_lifting f n k

end
end DaggerNativeCoproductDescFibration
