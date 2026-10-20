import OriginalSimplicialCategoryBarVertexHomotopy

/-!
# The original whole bar homotopy of original whole fibre precomposition

Assemble the actual original component cylinders on the native coproduct of
all original Hom objects. Every original endpoint remains present.
-/
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Opposite Simplicial DaggerModels
open scoped MonoidalCategory
open DaggerOriginalSimplicialCategoryBarConstruction
open DaggerOriginalSimplicialCategoryBarHomInclusion
open DaggerOriginalSimplicialCategoryBarCoproductDegrees
open DaggerOriginalSimplicialCategoryWholeBarFibreIso
open DaggerOriginalSimplicialCategoryWholeHomTransport
open DaggerOriginalSimplicialCategoryVertexComposition
open DaggerOriginalSimplicialCategoryBarVertexCylinder
open DaggerOriginalSimplicialCategoryBarVertexHomotopy
open DaggerNativeSSetCoproductHomotopy
universe u
namespace DaggerOriginalSimplicialCategoryWholeBarVertexHomotopy
noncomputable section

/-- The cylinder on the entire original Hom coproduct retains its original bar component. -/
def wholeBarVertexCylinderMap (C : SimplicialCat.{u, u}) {x y : C.Obj}
    (a : (C.enriched.Hom x y).obj (op ⦋0⦌)) :
    originalHomSum C y ⊗ Δ[1] ⟶ bar C :=
  coproductCylinderMap (barVertexHomotopy C a)

/-- The whole original cylinder acts by the exact original component cylinder at each endpoint. -/
theorem wholeBarVertexCylinderMap_apply (C : SimplicialCat.{u, u}) {x y : C.Obj}
    (a : (C.enriched.Hom x y).obj (op ⦋0⦌)) (n : SimplexCategoryᵒᵖ) (z : C.Obj)
    (b : (C.enriched.Hom y z).obj n) (t : Δ[1].obj n) :
    (wholeBarVertexCylinderMap C a).app n
        (coproductDegreeEquiv (C.enriched.Hom y) n ⟨z, b⟩, t) =
      barDegreeEquiv C n ⟨z, (barVertexCylinderMap C a z).app n (b, t)⟩ :=
  coproductCylinderDegree_apply (barVertexHomotopy C a) n z b t

/-- The entire original cylinder starts at inclusion after the actual whole precomposition. -/
theorem wholeBarVertexCylinderMap_zero (C : SimplicialCat.{u, u}) {x y : C.Obj}
    (a : (C.enriched.Hom x y).obj (op ⦋0⦌)) :
    SSet.ι₀ ≫ wholeBarVertexCylinderMap C a =
      wholeHomPrecompose C a ≫ wholeBarHomInclusion C x := by
  rw [wholeBarVertexCylinderMap, coproductCylinderMap_zero]
  apply Sigma.hom_ext
  intro z
  change Sigma.ι (C.enriched.Hom y) z ≫
      Limits.Sigma.map (fun z ↦ precomposeVertex C a z ≫ barHomInclusion C x z) =
    Sigma.ι (C.enriched.Hom y) z ≫
      (Limits.Sigma.map (fun z ↦ precomposeVertex C a z) ≫ wholeBarHomInclusion C x)
  rw [Sigma.ι_map, ← Category.assoc, Sigma.ι_map, Category.assoc]
  change _ = precomposeVertex C a z ≫
    (Sigma.ι (C.enriched.Hom x) z ≫
      Sigma.desc (fun z ↦ barHomInclusion C x z ≫ barInclusion C z))
  rw [Sigma.ι_desc]
  rfl

/-- The entire original cylinder ends at the original whole Hom inclusion. -/
theorem wholeBarVertexCylinderMap_one (C : SimplicialCat.{u, u}) {x y : C.Obj}
    (a : (C.enriched.Hom x y).obj (op ⦋0⦌)) :
    SSet.ι₁ ≫ wholeBarVertexCylinderMap C a = wholeBarHomInclusion C y := by
  rw [wholeBarVertexCylinderMap, coproductCylinderMap_one]
  rfl

/-- Actual whole Hom precomposition is connected inside the actual whole original bar. -/
def wholeBarVertexHomotopy (C : SimplicialCat.{u, u}) {x y : C.Obj}
    (a : (C.enriched.Hom x y).obj (op ⦋0⦌)) :
    SSet.Homotopy (wholeHomPrecompose C a ≫ wholeBarHomInclusion C x)
      (wholeBarHomInclusion C y) :=
  SSet.Homotopy.mk (wholeBarVertexCylinderMap C a) (wholeBarVertexCylinderMap_zero C a)
    (wholeBarVertexCylinderMap_one C a)

end
end DaggerOriginalSimplicialCategoryWholeBarVertexHomotopy
