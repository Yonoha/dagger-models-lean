import OriginalFullVertexPathFiberIso
import TopCatModelCategory.ModelCategorySSet

/-!
# Model consequences of the actual full-vertex path-fiber comparison

The strict comparison map is the map induced by the actual subcomplex inclusion.
Its isomorphism supplies a weak equivalence in the retained simplicial-set model.
When the ambient set is Kan, both endpoint maps are fibrations and both literal
fibers are fibrant. No new homotopy-fiber comparison API is postulated here.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

universe u

namespace DaggerOriginalFullVertexSubcomplex

noncomputable section

/-- The strict comparison is exactly the forward map of the constructed iso. -/
theorem strictPathFiberMap_isIso {X : SSet.{u}}
    (V : Set (X.obj (op ⦋0⦌)))
    (a b : (fullVertexSubcomplex X V : SSet).obj (op ⦋0⦌)) :
    IsIso (strictPathFiberMap (fullVertexSubcomplex X V).ι a b) := by
  change IsIso (strictPathFiberIso V a b).hom
  infer_instance

/-- The inclusion-induced map of the literal strict fibers is a weak equivalence. -/
theorem strictPathFiberMap_weakEquivalence {X : SSet.{u}}
    (V : Set (X.obj (op ⦋0⦌)))
    (a b : (fullVertexSubcomplex X V : SSet).obj (op ⦋0⦌)) :
    WeakEquivalence (strictPathFiberMap (fullVertexSubcomplex X V).ι a b) := by
  have : IsIso (strictPathFiberMap (fullVertexSubcomplex X V).ι a b) :=
    strictPathFiberMap_isIso V a b
  infer_instance

/-- The actual paired endpoint evaluation is a fibration for Kan objects. -/
theorem strictPathEndpoint_fibration (X : SSet.{u}) [SSet.KanComplex X] :
    Fibration X.pathEv₀₁ := by
  infer_instance

/-- The literal ambient path fiber is fibrant, by the retained fiber theorem. -/
theorem strictPathFiber_fibrant (X : SSet.{u}) [SSet.KanComplex X]
    (a b : X.obj (op ⦋0⦌)) :
    IsFibrant (strictPathFiber X a b : SSet) := by
  dsimp only [strictPathFiber]
  infer_instance

/-- Both endpoints may be chosen in an arbitrary full vertex subcomplex. -/
theorem fullVertexStrictPathFiber_fibrant {X : SSet.{u}} [SSet.KanComplex X]
    (V : Set (X.obj (op ⦋0⦌)))
    (a b : (fullVertexSubcomplex X V : SSet).obj (op ⦋0⦌)) :
    IsFibrant (strictPathFiber (fullVertexSubcomplex X V : SSet) a b : SSet) := by
  dsimp only [strictPathFiber]
  infer_instance

end

end DaggerOriginalFullVertexSubcomplex
