import NativeGroupoidChainExtension
import NativePalindromicVertexFold
import NativeRealEdgewiseTargetWeak

/-! An exact palindromic section of the ORIGINAL edgewise projection on groupoid nerves. -/
set_option autoImplicit false
open CategoryTheory Opposite Simplicial AugmentedSimplexCategory HomotopicalAlgebra
open DaggerNativeGroupoidChainExtension DaggerNativePalindromicVertexFold
open DaggerNativeRealEdgewiseIndex DaggerNativeRealEdgewiseSSet
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerNativeGroupoidPalindromicSection
noncomputable section
variable (C : Type u) [Groupoid.{u} C]

/-- The original chain, preceded by its inverse chain and the central identity. -/
def fold (n : SimplexCategory) (F : Fin (n.len + 1) ⥤ C) :
    Fin ((epsilon.obj n).len + 1) ⥤ C := ofVertices F (vertex n)

/-- The full native simplex operators commute with the whole palindromic chain. -/
theorem fold_natural {n m : SimplexCategory} (a : n ⟶ m) (F : Fin (m.len + 1) ⥤ C) :
    fold C n ((SimplexCategory.toCat.map a).toFunctor ⋙ F) =
      (SimplexCategory.toCat.map (epsilon.map a)).toFunctor ⋙ fold C m F := by
  unfold fold
  rw [ofVertices_chain_precomp, ofVertices_precomp]
  apply congrArg (ofVertices F)
  funext k
  exact (vertex_naturality a k).symm

/-- Taking the unchanged native right half returns the ENTIRE original chain. -/
theorem fold_projection (n : SimplexCategory) (F : Fin (n.len + 1) ⥤ C) :
    (SimplexCategory.toCat.map (inr' n n)).toFunctor ⋙ fold C n F = F := by
  unfold fold
  rw [ofVertices_precomp]
  have hv : vertex n ∘ (SimplexCategory.toCat.map (inr' n n)).toFunctor.obj = id := by
    funext i
    exact vertex_right n i
  rw [hv]
  refine CategoryTheory.Functor.ext (fun _ ↦ rfl) ?_
  intro i j f
  simpa only [eqToHom_refl, Category.comp_id, Category.id_comp] using bridge_hom F f

/-- A genuine simplicial map on the SAME original nerve and edgewise index. -/
def sectionMap : nerve C ⟶ edgewise.obj (nerve C) where
  app n F := fold C n.unop F
  naturality _ _ a := by
    funext F
    exact fold_natural C a.unop F

theorem section_projection : sectionMap C ≫ targetProjection (nerve C) = 𝟙 (nerve C) := by
  apply NatTrans.ext
  funext n F
  exact fold_projection C n.unop F

/-- Use the OLD projection weak theorem, without a new Arrow-nerve identification. -/
theorem section_weak : WeakEquivalence (sectionMap C) := by
  have : WeakEquivalence (targetProjection (nerve C)) :=
    DaggerNativeRealEdgewiseTargetWeak.targetProjection_weak (nerve C)
  exact weakEquivalence_of_postcomp_of_fac (section_projection C)

/-- Every original vertex is its SAME canonical identity-arrow vertex after edgewise. -/
theorem section_vertex (x : C) :
    (sectionMap C).app (op ⦋0⦌) (ComposableArrows.mk₀ x) =
      (nerve C).σ (0 : Fin 1) (ComposableArrows.mk₀ x) := by
  refine CategoryTheory.Functor.ext (fun _ ↦ rfl) ?_
  intro i j f
  simp only [eqToHom_refl, Category.comp_id, Category.id_comp]
  change inv (𝟙 x) ≫ 𝟙 x = 𝟙 x
  simp

end
end DaggerNativeGroupoidPalindromicSection
