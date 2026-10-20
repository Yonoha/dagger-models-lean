import NativeCoherentCotensorConstants
import NativeBisimplicialDiagonal

/-! The actual cotensor resolution of the SAME original coherent nerve, with literal constants. -/
set_option autoImplicit false
open CategoryTheory Opposite Simplicial DaggerModels OrdinaryRigidification
open DaggerOriginalCotensorPrecompositionWeak DaggerNativeCoherentCotensorConstants
open DaggerNativeBisimplicialDiagonal
universe u
namespace DaggerOriginalCoherentCotensorResolution
noncomputable section

def parameterDiagram (C : SimplicialCat.{u, u}) : SimplexCategoryᵒᵖ ⥤ SimplicialCat.{u, u} where
  obj n := originalCotensor (SSet.stdSimplex.obj n.unop) C
  map a := restrictionFunctor (SSet.stdSimplex.map a.unop) C
  map_id n := by
    rw [unop_id, CategoryTheory.Functor.map_id]
    exact restriction_id _ C
  map_comp a b := by
    rw [unop_comp, SSet.stdSimplex.map_comp]
    exact restriction_comp (SSet.stdSimplex.map b.unop) (SSet.stdSimplex.map a.unop) C

def resolution (C : SimplicialCat.{u, u}) : SimplexCategoryᵒᵖ ⥤ SSet.{u} :=
  parameterDiagram C ⋙ coherentNerve

def constantDiagram (C : SimplicialCat.{u, u}) : SimplexCategoryᵒᵖ ⥤ SSet.{u} :=
  (Functor.const SimplexCategoryᵒᵖ).obj (coherentNerve.obj C)

def constantComparison (C : SimplicialCat.{u, u}) : constantDiagram C ⟶ resolution C where
  app n := coherentNerve.map (constantFunctor (SSet.stdSimplex.obj n.unop) C)
  naturality n m a := by
    change (𝟙 (coherentNerve.obj C)) ≫
      coherentNerve.map (constantFunctor (SSet.stdSimplex.obj m.unop) C) =
        coherentNerve.map (constantFunctor (SSet.stdSimplex.obj n.unop) C) ≫
          coherentNerve.map (restrictionFunctor (SSet.stdSimplex.map a.unop) C)
    rw [Category.id_comp, ← coherentNerve.map_comp, constant_parameter]

def diagonalConstantIso (X : SSet.{u}) :
    diagonalFunctor.obj ((Functor.const SimplexCategoryᵒᵖ).obj X) ≅ X :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (by intros; rfl)

def comparison (C : SimplicialCat.{u, u}) :
    coherentNerve.obj C ⟶ diagonalFunctor.obj (resolution C) :=
  (diagonalConstantIso (coherentNerve.obj C)).inv ≫ diagonalFunctor.map (constantComparison C)

/-- The full vertex map is the SAME coherent-nerve constant functor at the actual unit simplex. -/
theorem comparison_vertex (C : SimplicialCat.{u, u})
    (x : (coherentNerve.obj C).obj (op ⦋0⦌)) :
    NerveVertices.vertexEquiv (originalCotensor (SSet.stdSimplex.obj ⦋0⦌) C)
      ((comparison C).app (op ⦋0⦌) x) = NerveVertices.vertexEquiv C x :=
  DaggerNativeGroupoidalCoherentNerveWeak.vertex_map
    (constantFunctor (SSet.stdSimplex.obj ⦋0⦌) C) x

end
end DaggerOriginalCoherentCotensorResolution
