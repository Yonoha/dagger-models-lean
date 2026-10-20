import OriginalSimplicialCategoryWholeFibreTransportNaturality

/-!
# The actual original bar arrow of precomposition

For an original vertex a : x → y and an original n-simplex b : y → z,
the native over-category arrow from ab to b has underlying arrow a.
Its walking-arrow diagram commutes with every original degree operator.
-/
set_option autoImplicit false
open CategoryTheory Opposite Simplicial DaggerModels
open DaggerOriginalSimplicialDegreeCategory
open DaggerOriginalSimplicialCategoryOverDiagram
open DaggerOriginalSimplicialCategoryVertexComposition
universe u
namespace DaggerOriginalSimplicialCategoryBarVertexArrow
noncomputable section

/-- The original commuting triangle from the precomposed arrow to the original arrow. -/
def vertexOverArrow (C : SimplicialCat.{u, u}) {x y : C.Obj}
    (a : (C.enriched.Hom x y).obj (op ⦋0⦌)) (z : C.Obj) (n : SimplexCategoryᵒᵖ)
    (b : (C.enriched.Hom y z).obj n) :
    Over.mk (T := degreeObjects C n) ((precomposeVertex C a z).app n b) ⟶
      Over.mk (T := degreeObjects C n) b :=
  Over.homMk (T := degreeObjects C n) ((vertexPoint C a).app n PUnit.unit) rfl

/-- The native walking-arrow diagram of the original precomposition triangle. -/
def vertexOverDiagram (C : SimplicialCat.{u, u}) {x y : C.Obj}
    (a : (C.enriched.Hom x y).obj (op ⦋0⦌)) (z : C.Obj) (n : SimplexCategoryᵒᵖ)
    (b : (C.enriched.Hom y z).obj n) : Fin 2 ⥤ overObjects C z n :=
  ComposableArrows.mk₁ (vertexOverArrow C a z n b)

/-- Every original simplicial operator preserves the entire original walking-arrow diagram. -/
theorem vertexOverDiagram_map (C : SimplicialCat.{u, u}) {x y : C.Obj}
    (a : (C.enriched.Hom x y).obj (op ⦋0⦌)) (z : C.Obj)
    {n m : SimplexCategoryᵒᵖ} (i : n ⟶ m) (b : (C.enriched.Hom y z).obj n) :
    vertexOverDiagram C a z m ((C.enriched.Hom y z).map i b) =
      vertexOverDiagram C a z n b ⋙ overDegreeMap C z i := by
  have hobj : ∀ k, (vertexOverDiagram C a z m
      ((C.enriched.Hom y z).map i b)).obj k =
        (vertexOverDiagram C a z n b ⋙ overDegreeMap C z i).obj k := by
    intro k
    fin_cases k
    · apply Comma.ext (x := Over.mk (T := degreeObjects C m)
        ((precomposeVertex C a z).app m ((C.enriched.Hom y z).map i b)))
        (y := (overDegreeMap C z i).obj
          (Over.mk (T := degreeObjects C n) ((precomposeVertex C a z).app n b)))
        rfl rfl
      exact heq_of_eq (congrFun ((precomposeVertex C a z).naturality i) b)
    · rfl
  refine Functor.hext hobj ?_
  intro k l f
  apply overHom_heq (hobj k) (hobj l)
  fin_cases k <;> fin_cases l
  · simp [vertexOverDiagram, ComposableArrows.mk₁, ComposableArrows.Mk₁.obj,
      ComposableArrows.Mk₁.map, overDegreeMap, Over.post]
    exact (degreeMap C i).map_id x |>.symm
  · have hp := congrFun ((vertexPoint C a).naturality i) PUnit.unit
    change (vertexPoint C a).app m PUnit.unit =
      (C.enriched.Hom x y).map i ((vertexPoint C a).app n PUnit.unit) at hp
    simpa [vertexOverDiagram, vertexOverArrow, ComposableArrows.mk₁,
      ComposableArrows.Mk₁.obj, ComposableArrows.Mk₁.map, overDegreeMap, Over.post,
      Over.homMk] using heq_of_eq hp
  · have ht : (1 : Fin 2) ≤ 0 := leOfHom f
    norm_num at ht
  · simp [vertexOverDiagram, ComposableArrows.mk₁, ComposableArrows.Mk₁.obj,
      ComposableArrows.Mk₁.map, overDegreeMap, Over.post]
    exact (degreeMap C i).map_id y |>.symm

/-- Forgetting the original commuting triangle retains precisely the original vertex arrow. -/
theorem vertexOverDiagram_forget (C : SimplicialCat.{u, u}) {x y : C.Obj}
    (a : (C.enriched.Hom x y).obj (op ⦋0⦌)) (z : C.Obj) (n : SimplexCategoryᵒᵖ)
    (b : (C.enriched.Hom y z).obj n) :
    vertexOverDiagram C a z n b ⋙ Over.forget (T := degreeObjects C n) z =
      ComposableArrows.mk₁ (C := degreeObjects C n)
        ((vertexPoint C a).app n PUnit.unit) := by
  refine Functor.hext (fun k ↦ ?_) ?_
  · fin_cases k <;> rfl
  · intro k l f
    fin_cases k <;> fin_cases l
    · rfl
    · rfl
    · have ht : (1 : Fin 2) ≤ 0 := leOfHom f
      norm_num at ht
    · rfl

end
end DaggerOriginalSimplicialCategoryBarVertexArrow
