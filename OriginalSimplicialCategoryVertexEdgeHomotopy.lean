import OriginalSimplicialCategoryVertexComposition
import OriginalSimplicialCategoryWholeBarFibreLocalization

/-!
# Original Hom edges induce homotopies of original composition maps

An original edge gives a native homotopy of its original point maps. Native
whiskering, precomposition and postcomposition turn it into a homotopy of
precomposition on the whole original Hom simplicial set.
-/
set_option autoImplicit false
open CategoryTheory MonoidalCategory Opposite Simplicial DaggerModels
open DaggerOriginalSimplicialCategoryVertexComposition
universe u
namespace DaggerOriginalSimplicialCategoryVertexEdgeHomotopy
noncomputable section

/-- Each original Hom edge gives a homotopy of its actual original point maps. -/
def vertexPointEdgeHomotopy (C : SimplicialCat.{u, u}) {x y : C.Obj}
    {a b : (C.enriched.Hom x y).obj (op ⦋0⦌)} (e : SSet.Edge a b) :
    SSet.Homotopy (vertexPoint C a) (vertexPoint C b) :=
  SSet.Homotopy.mk ((λ_ (Δ[1] : SSet.{u})).hom ≫ SSet.yonedaEquiv.symm e.edge) (by
    apply (SSet.unitHomEquiv (C.enriched.Hom x y)).injective
    simp only [vertexPoint, Equiv.apply_symm_apply]
    change (SSet.yonedaEquiv.symm e.edge).app (op ⦋0⦌)
      ((SSet.const (X := 𝟙_ SSet.{u})
        ((SSet.stdSimplex.obj₀Equiv (n := 1)).symm 0)).app (op ⦋0⦌) PUnit.unit) = a
    rw [SSet.yonedaEquiv_symm_app_apply (X := C.enriched.Hom x y)
      (n := op ⦋1⦌) (m := op ⦋0⦌) e.edge]
    convert e.src_eq using 1
    apply congrArg (fun f : ⦋0⦌ ⟶ ⦋1⦌ ↦ (C.enriched.Hom x y).map f.op e.edge)
    ext i
    fin_cases i
    rfl) (by
    apply (SSet.unitHomEquiv (C.enriched.Hom x y)).injective
    simp only [vertexPoint, Equiv.apply_symm_apply]
    change (SSet.yonedaEquiv.symm e.edge).app (op ⦋0⦌)
      ((SSet.const (X := 𝟙_ SSet.{u})
        ((SSet.stdSimplex.obj₀Equiv (n := 1)).symm 1)).app (op ⦋0⦌) PUnit.unit) = b
    rw [SSet.yonedaEquiv_symm_app_apply (X := C.enriched.Hom x y)
      (n := op ⦋1⦌) (m := op ⦋0⦌) e.edge]
    convert e.tgt_eq using 1
    apply congrArg (fun f : ⦋0⦌ ⟶ ⦋1⦌ ↦ (C.enriched.Hom x y).map f.op e.edge)
    ext i
    fin_cases i
    rfl)

/-- The actual edge gives a homotopy of precomposition on the entire original Hom. -/
def precomposeVertexEdgeHomotopy (C : SimplicialCat.{u, u}) {x y : C.Obj}
    {a b : (C.enriched.Hom x y).obj (op ⦋0⦌)} (e : SSet.Edge a b) (z : C.Obj) :
    SSet.Homotopy (precomposeVertex C a z) (precomposeVertex C b z) :=
  (((vertexPointEdgeHomotopy C e).whiskerRight (C.enriched.Hom y z)).precomp
    (λ_ (C.enriched.Hom y z)).inv).postcomp (C.enriched.comp x y z)

end
end DaggerOriginalSimplicialCategoryVertexEdgeHomotopy
