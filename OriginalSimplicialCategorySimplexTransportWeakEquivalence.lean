import OriginalSimplicialCategorySimplexTransport
import NativeSimplexParameterWeakMap

/-!
# Original pi0 groupoids act weakly through every original Hom simplex family

The actual original simplex and actual original composition are retained.
Only invertibility of its original first-vertex component is needed; the
original pi0 groupoid hypothesis supplies it for every simplex. Neither Kan
nor cofibrancy assumptions are added to the original Hom objects.
-/
set_option autoImplicit false
open CategoryTheory Opposite Simplicial DaggerModels HomotopicalAlgebra
open DaggerOriginalSimplicialPiZeroCategory DaggerOriginalAmbientDaggerPiZeroGroupoid
open DaggerOriginalSimplicialCategoryVertexTransportWeakEquivalence
open DaggerOriginalSimplicialCategoryGroupoidHomTransport
open DaggerOriginalSimplicialCategorySimplexTransport
open DaggerNativeSimplexParameterWeakMap
universe u
namespace DaggerOriginalSimplicialCategorySimplexTransportWeakEquivalence
noncomputable section

/-- An invertible original first-vertex component makes the entire simplex family weak. -/
theorem simplexPrecompose_weakEquivalence_of_isIso (C : SimplicialCat.{u, u})
    {x y : C.Obj} {n : ℕ} (σ : (C.enriched.Hom x y).obj (op ⦋n⦌))
    (hσ : @IsIso (componentObjects C) (componentCategory C) x y
      (SSet.π₀.mk (simplexFirstVertex C σ))) (z : C.Obj) :
    WeakEquivalence (simplexPrecompose C σ z) := by
  apply parameterizedMap_weakEquivalence
  rw [simplexPrecompose_firstVertex]
  exact precomposeVertex_weakEquivalence C (simplexFirstVertex C σ) hσ z

/-- Every original Hom simplex family is weak when the exact original pi0 is a groupoid. -/
theorem simplexPrecompose_weakEquivalence_of_actualGroupoid (C : SimplicialCat.{u, u})
    (hC : HasActualComponentGroupoid C) {x y : C.Obj} {n : ℕ}
    (σ : (C.enriched.Hom x y).obj (op ⦋n⦌)) (z : C.Obj) :
    WeakEquivalence (simplexPrecompose C σ z) := by
  apply parameterizedMap_weakEquivalence
  rw [simplexPrecompose_firstVertex]
  exact precomposeVertex_weakEquivalence_of_actualGroupoid C hC (simplexFirstVertex C σ) z

/-- Invertibility also makes the full original parameter-preserving relative map weak. -/
theorem relativeSimplexPrecompose_weakEquivalence_of_isIso (C : SimplicialCat.{u, u})
    {x y : C.Obj} {n : ℕ} (σ : (C.enriched.Hom x y).obj (op ⦋n⦌))
    (hσ : @IsIso (componentObjects C) (componentCategory C) x y
      (SSet.π₀.mk (simplexFirstVertex C σ))) (z : C.Obj) :
    WeakEquivalence (relativeSimplexPrecompose C σ z) := by
  apply relativeParameterizedMap_weakEquivalence
  rw [simplexPrecompose_firstVertex]
  exact precomposeVertex_weakEquivalence C (simplexFirstVertex C σ) hσ z

/-- Every relative original simplex transport is weak under the actual pi0 groupoid hypothesis. -/
theorem relativeSimplexPrecompose_weakEquivalence_of_actualGroupoid
    (C : SimplicialCat.{u, u}) (hC : HasActualComponentGroupoid C) {x y : C.Obj} {n : ℕ}
    (σ : (C.enriched.Hom x y).obj (op ⦋n⦌)) (z : C.Obj) :
    WeakEquivalence (relativeSimplexPrecompose C σ z) := by
  apply relativeParameterizedMap_weakEquivalence
  rw [simplexPrecompose_firstVertex]
  exact precomposeVertex_weakEquivalence_of_actualGroupoid C hC (simplexFirstVertex C σ) z

end
end DaggerOriginalSimplicialCategorySimplexTransportWeakEquivalence
