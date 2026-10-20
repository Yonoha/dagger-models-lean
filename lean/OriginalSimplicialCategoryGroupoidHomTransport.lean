import OriginalSimplicialCategoryVertexTransportWeakEquivalence
import OriginalAmbientDaggerPiZeroGroupoid

/-!
# Original pi0 groupoids act weakly by transport on whole original Hom objects

Use the established predicate requiring a groupoid structure on exactly the
original component category, with its entire underlying category unchanged.
All original vertex precomposition maps are weak, without original Hom Kan
or cofibrancy hypotheses.
-/
set_option autoImplicit false
open CategoryTheory MonoidalCategory Opposite Simplicial DaggerModels HomotopicalAlgebra
open DaggerOriginalSimplicialPiZeroCategory
open DaggerOriginalAmbientDaggerPiZeroGroupoid
open DaggerOriginalSimplicialCategoryVertexComposition
open DaggerOriginalSimplicialCategoryVertexTransportWeakEquivalence
universe u
namespace DaggerOriginalSimplicialCategoryGroupoidHomTransport
noncomputable section

/-- The actual original pi0 groupoid makes every original Hom precomposition weak. -/
theorem precomposeVertex_weakEquivalence_of_actualGroupoid (C : SimplicialCat.{u, u})
    (hC : HasActualComponentGroupoid C) {x y : C.Obj}
    (a : (C.enriched.Hom x y).obj (op ⦋0⦌)) (z : C.Obj) :
    WeakEquivalence (precomposeVertex C a z) := by
  obtain ⟨G, hG⟩ := hC
  have hi : ∀ {r s : componentObjects C} (f : r ⟶ s), IsIso f := by
    rw [← hG]
    intro r s f
    let g : Groupoid.{u, u} (componentObjects C) := G
    infer_instance
  exact precomposeVertex_weakEquivalence C a (hi (r := x) (s := y) (SSet.π₀.mk a)) z

end
end DaggerOriginalSimplicialCategoryGroupoidHomTransport
