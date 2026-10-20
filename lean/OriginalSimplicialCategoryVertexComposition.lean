import OriginalSimplicialPiZeroCategory

/-!
# Composition with actual original vertices on full original Hom simplicial sets

Every vertex determines its native unit-to-Hom map. Original enriched
composition gives the full precomposition and postcomposition maps.
The degree categories retain the original composition in every degree.
-/
set_option autoImplicit false
open CategoryTheory MonoidalCategory Opposite Simplicial DaggerModels
open DaggerOriginalSimplicialDegreeCategory
open DaggerOriginalSimplicialPiZeroLaxMonoidal
universe u
namespace DaggerOriginalSimplicialCategoryVertexComposition
noncomputable section

/-- The native point map of precisely the original Hom vertex. -/
def vertexPoint (C : SimplicialCat.{u, u}) {x y : C.Obj}
    (a : (C.enriched.Hom x y).obj (op ⦋0⦌)) : 𝟙_ SSet.{u} ⟶ C.enriched.Hom x y :=
  (SSet.unitHomEquiv (C.enriched.Hom x y)).symm a

/-- The original point map evaluates to its exact original vertex. -/
theorem vertexPoint_zero (C : SimplicialCat.{u, u}) {x y : C.Obj}
    (a : (C.enriched.Hom x y).obj (op ⦋0⦌)) :
    (vertexPoint C a).app (op ⦋0⦌) PUnit.unit = a :=
  (SSet.unitHomEquiv (C.enriched.Hom x y)).apply_symm_apply a

/-- Original precomposition acts on every simplex of the whole original Hom object. -/
def precomposeVertex (C : SimplicialCat.{u, u}) {x y : C.Obj}
    (a : (C.enriched.Hom x y).obj (op ⦋0⦌)) (z : C.Obj) :
    C.enriched.Hom y z ⟶ C.enriched.Hom x z :=
  leftVertexInclusion (C.enriched.Hom x y) (C.enriched.Hom y z) a ≫ C.enriched.comp x y z

/-- Original postcomposition acts on every simplex of the whole original Hom object. -/
def postcomposeVertex (C : SimplicialCat.{u, u}) (w : C.Obj) {x y : C.Obj}
    (a : (C.enriched.Hom x y).obj (op ⦋0⦌)) :
    C.enriched.Hom w x ⟶ C.enriched.Hom w y :=
  rightVertexInclusion (C.enriched.Hom w x) (C.enriched.Hom x y) a ≫ C.enriched.comp w x y

/-- Precomposition evaluates to native composition in the exact original degree category. -/
theorem precomposeVertex_apply (C : SimplicialCat.{u, u}) {x y : C.Obj}
    (a : (C.enriched.Hom x y).obj (op ⦋0⦌)) (z : C.Obj) (n : SimplexCategoryᵒᵖ)
    (b : (C.enriched.Hom y z).obj n) :
    (precomposeVertex C a z).app n b =
      @CategoryStruct.comp (degreeObjects C n) (degreeCategory C n).toCategoryStruct x y z
        ((vertexPoint C a).app n PUnit.unit) b := rfl

/-- Postcomposition evaluates to native composition in the exact original degree category. -/
theorem postcomposeVertex_apply (C : SimplicialCat.{u, u}) (w : C.Obj) {x y : C.Obj}
    (a : (C.enriched.Hom x y).obj (op ⦋0⦌)) (n : SimplexCategoryᵒᵖ)
    (b : (C.enriched.Hom w x).obj n) :
    (postcomposeVertex C w a).app n b =
      @CategoryStruct.comp (degreeObjects C n) (degreeCategory C n).toCategoryStruct w x y
        b ((vertexPoint C a).app n PUnit.unit) := rfl

/-- The native point of the original identity vertex is the actual enriched identity. -/
theorem vertexPoint_id (C : SimplicialCat.{u, u}) (x : C.Obj) :
    vertexPoint C ((C.enriched.id x).app (op ⦋0⦌) PUnit.unit) = C.enriched.id x :=
  (SSet.unitHomEquiv (C.enriched.Hom x x)).symm_apply_apply (C.enriched.id x)

/-- Original identity precomposition is the identity of the whole original Hom object. -/
theorem precomposeVertex_id (C : SimplicialCat.{u, u}) (x z : C.Obj) :
    precomposeVertex C ((C.enriched.id x).app (op ⦋0⦌) PUnit.unit) z =
      𝟙 (C.enriched.Hom x z) := by
  apply NatTrans.ext
  funext n b
  rw [precomposeVertex_apply, vertexPoint_id]
  exact @Category.id_comp (degreeObjects C n) (degreeCategory C n) x z b

/-- Original identity postcomposition is the identity of the whole original Hom object. -/
theorem postcomposeVertex_id (C : SimplicialCat.{u, u}) (w x : C.Obj) :
    postcomposeVertex C w ((C.enriched.id x).app (op ⦋0⦌) PUnit.unit) =
      𝟙 (C.enriched.Hom w x) := by
  apply NatTrans.ext
  funext n b
  rw [postcomposeVertex_apply, vertexPoint_id]
  exact @Category.comp_id (degreeObjects C n) (degreeCategory C n) w x b

/-- The point of an original composite is the actual composite of its original point maps. -/
theorem vertexPoint_comp (C : SimplicialCat.{u, u}) {x y z : C.Obj}
    (a : (C.enriched.Hom x y).obj (op ⦋0⦌))
    (b : (C.enriched.Hom y z).obj (op ⦋0⦌)) :
    vertexPoint C ((C.enriched.comp x y z).app (op ⦋0⦌) (a, b)) =
      vertexPoint C b ≫ precomposeVertex C a z := by
  apply (SSet.unitHomEquiv (C.enriched.Hom x z)).injective
  change (vertexPoint C ((C.enriched.comp x y z).app (op ⦋0⦌) (a, b))).app
      (op ⦋0⦌) PUnit.unit =
    (precomposeVertex C a z).app (op ⦋0⦌) ((vertexPoint C b).app (op ⦋0⦌) PUnit.unit)
  rw [vertexPoint_zero, vertexPoint_zero, precomposeVertex_apply, vertexPoint_zero]
  rfl

/-- Original precomposition preserves composition on all simplices of the original Hom. -/
theorem precomposeVertex_comp (C : SimplicialCat.{u, u}) {w x y : C.Obj}
    (a : (C.enriched.Hom x y).obj (op ⦋0⦌))
    (b : (C.enriched.Hom w x).obj (op ⦋0⦌)) (z : C.Obj) :
    precomposeVertex C a z ≫ precomposeVertex C b z =
      precomposeVertex C ((C.enriched.comp w x y).app (op ⦋0⦌) (b, a)) z := by
  apply NatTrans.ext
  funext n h
  change (precomposeVertex C b z).app n ((precomposeVertex C a z).app n h) = _
  rw [precomposeVertex_apply, precomposeVertex_apply, precomposeVertex_apply,
    vertexPoint_comp]
  exact (@Category.assoc (degreeObjects C n) (degreeCategory C n) w x y z
    ((vertexPoint C b).app n PUnit.unit) ((vertexPoint C a).app n PUnit.unit) h).symm

end
end DaggerOriginalSimplicialCategoryVertexComposition
