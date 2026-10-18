import NativeTopCatPullbackFromInducing
import TopCatModelCategory.TopCat.ToTopProducts
import TopCatModelCategory.ModelCategoryTopCat

/-!
# Actual realization preserves pullbacks along simplicial monomorphisms

The native realization-forget functor preserves finite limits of sets.
The top leg of a pullback along a monomorphism realizes to a closed embedding.
The inducing-leg criterion therefore recovers the actual TopCat pullback,
without assuming realization preserves arbitrary TopCat finite products.
-/
set_option autoImplicit false
open CategoryTheory Limits Topology
open DaggerNativeTopCatPullbackFromInducing
universe u
namespace DaggerNativeRealizationMonomorphismPullbacks
noncomputable section

/-- Realizing the original four maps preserves a pullback along a monomorphism. -/
theorem realization_isPullback_of_mono
    {W X Y Z : SSet.{u}} {t : W ⟶ X} {l : W ⟶ Y} {r : X ⟶ Z} {b : Y ⟶ Z}
    (h : IsPullback t l r b) [Mono b] :
    IsPullback (SSet.toTop.map t) (SSet.toTop.map l)
      (SSet.toTop.map r) (SSet.toTop.map b) := by
  have ht : Mono t := by
    have ht' : h.isoPullback.hom ≫ pullback.fst r b = t := by simp
    rw [← ht']
    infer_instance
  apply isPullback_of_underlying_isPullback_of_isInducing
  · exact h.map (SSet.toTop ⋙ forget TopCat)
  · exact (SSet.closedEmbeddings_toObj_map_of_mono t).isEmbedding.isInducing

end
end DaggerNativeRealizationMonomorphismPullbacks
