import ActualQWeightedAugmentationCoproducts

/-! Native reindexed coproduct maps are weak for bijective indices and weak component maps. -/
set_option autoImplicit false
open CategoryTheory Limits HomotopicalAlgebra
open DaggerSSetGluing
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerNativeCoproductReindexedWeak
noncomputable section

theorem map'_factor {I J : Type u} {X : I → SSet.{u}} {Y : J → SSet.{u}}
    (r : I → J) (hr : Function.Bijective r) (f : ∀ i, X i ⟶ Y (r i)) :
    Limits.Sigma.map' r f = Limits.Sigma.map f ≫
      (Limits.Sigma.reindex (Equiv.ofBijective r hr) Y).hom := by
  apply Limits.Sigma.hom_ext
  intro i
  rw [← Category.assoc, Limits.Sigma.ι_map, Category.assoc]
  have hi : Limits.Sigma.ι (fun i ↦ Y (r i)) i ≫
      (Limits.Sigma.reindex (Equiv.ofBijective r hr) Y).hom = Limits.Sigma.ι Y (r i) :=
    Limits.Sigma.ι_reindex_hom (Equiv.ofBijective r hr) Y i
  rw [hi]
  exact Limits.Sigma.ι_comp_map' r f i

theorem map'_weak {I J : Type u} {X : I → SSet.{u}} {Y : J → SSet.{u}}
    (r : I → J) (hr : Function.Bijective r) (f : ∀ i, X i ⟶ Y (r i))
    (hf : ∀ i, WeakEquivalence (f i)) : WeakEquivalence (Limits.Sigma.map' r f) := by
  have : WeakEquivalence (Limits.Sigma.map f) := (weakEquivalence_iff_GW _).mpr
    (DaggerOriginalFlagFlankification.sigmaMap_GW f
      (fun i ↦ (weakEquivalence_iff_GW _).mp (hf i)))
  rw [map'_factor r hr f]
  infer_instance

end
end DaggerNativeCoproductReindexedWeak
