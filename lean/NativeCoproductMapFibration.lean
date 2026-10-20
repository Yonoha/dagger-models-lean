import NativeCoproductKan

/-! Coproducts of actual Kan fibrations are Kan fibrations, without fibrant objects. -/
set_option autoImplicit false
open CategoryTheory Limits Simplicial Opposite HomotopicalAlgebra
open DaggerNativeCoproductConnectedFactor DaggerNativeSSetCoproductSummandFibration
open DaggerOriginalSimplicialCategoryBarCoproductDegrees
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerNativeCoproductMapFibration
noncomputable section

theorem sigma_map_horn_lifting {I : Type u} {X Y : I → SSet.{u}}
    (f : ∀ i, X i ⟶ Y i) [∀ i, Fibration (f i)] (n : ℕ) (k : Fin (n + 2)) :
    HasLiftingProperty (SSet.horn (n + 1) k).ι (Limits.Sigma.map f) where
  sq_hasLift := by
    intro a b sq
    obtain ⟨v⟩ := hornVertex_nonempty n k
    obtain ⟨⟨i, t⟩, ht⟩ := (coproductDegreeEquiv X (op ⦋0⦌)).surjective
      (a.app (op ⦋0⦌) v)
    obtain ⟨g, hg⟩ := connected_factor_fixed_summand X i a v t ht.symm
    obtain ⟨j, l, hl⟩ := simplex_factor_summand Y (n + 1) b
    have he : g ≫ f i ≫ Limits.Sigma.ι Y i =
        (SSet.horn (n + 1) k).ι ≫ l ≫ Limits.Sigma.ι Y j := by
      rw [← Limits.Sigma.ι_map, ← Category.assoc, hg, sq.w]
      rw [← hl]
    have hv := congrFun (NatTrans.congr_app he (op ⦋0⦌)) v
    have hij : i = j := (Sigma.mk.inj
      ((coproductDegreeEquiv Y (op ⦋0⦌)).injective hv)).1
    cases hij
    have hsq : CommSq g (SSet.horn (n + 1) k).ι (f i) l := ⟨by
      apply (cancel_mono (Limits.Sigma.ι Y i)).mp
      simpa only [Category.assoc] using he⟩
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
    · rw [Category.assoc, Limits.Sigma.ι_map, ← Category.assoc, hsq.fac_right, hl]

theorem sigma_map_fibration {I : Type u} {X Y : I → SSet.{u}}
    (f : ∀ i, X i ⟶ Y i) [∀ i, Fibration (f i)] :
    Fibration (Limits.Sigma.map f) := by
  rw [SSet.modelCategoryQuillen.fibration_iff]
  intro P Q j hj
  simp only [SSet.modelCategoryQuillen.J, MorphismProperty.iSup_iff] at hj
  obtain ⟨n, ⟨k⟩⟩ := hj
  exact sigma_map_horn_lifting f n k

end
end DaggerNativeCoproductMapFibration
