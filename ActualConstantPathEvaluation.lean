import ActualThinConstantCoherentNerve
import OriginalUnitaryDiscreteRecovered

/-! Every map from the actual path nerve to a constant set has its exact endpoint value. -/
set_option autoImplicit false
open CategoryTheory Opposite Simplicial DaggerModels
open DaggerUnitaryDiscrete DaggerActualThickeningPathContractibility
universe u
namespace DaggerActualConstantPathEvaluation
noncomputable section

variable {J : Type u} [LinearOrder J] (i j : J) (hij : i ≤ j)

theorem vertex_component_eq_shortest (P : SimplicialThickening.Path i j) :
    SSet.π₀.mk (X := nerve (SimplicialThickening.Path i j)) (ComposableArrows.mk₀ P) =
      SSet.π₀.mk (ComposableArrows.mk₀ (shortestPath i j hij)) := by
  exact (SSet.π₀.sound
    (X := nerve (SimplicialThickening.Path i j))
    (x₀ := ComposableArrows.mk₀ (shortestPath i j hij))
    (x₁ := ComposableArrows.mk₀ P)
    (ComposableArrows.mk₁ ((centerToId i j hij).app P))
    (ComposableArrows.ext₀ rfl) (ComposableArrows.ext₀ rfl)).symm

theorem simplex_component_eq_shortest (n : SimplexCategoryᵒᵖ)
    (γ : (nerve (SimplicialThickening.Path i j)).obj n) :
    simplexComponent (nerve (SimplicialThickening.Path i j)) n γ =
      SSet.π₀.mk (ComposableArrows.mk₀ (shortestPath i j hij)) := by
  have h0 : (nerve (SimplicialThickening.Path i j)).map
      (⦋0⦌.const n.unop 0).op γ = ComposableArrows.mk₀ (γ.obj 0) :=
    ComposableArrows.ext₀ rfl
  change SSet.π₀.mk (X := nerve (SimplicialThickening.Path i j))
    ((nerve (SimplicialThickening.Path i j)).map (⦋0⦌.const n.unop 0).op γ) = _
  rw [h0]
  exact vertex_component_eq_shortest i j hij (γ.obj 0)

theorem map_eq_shortest {B : Type u}
    (f : nerve (SimplicialThickening.Path i j) ⟶ constSSet B)
    (n : SimplexCategoryᵒᵖ) (γ : (nerve (SimplicialThickening.Path i j)).obj n) :
    f.app n γ = f.app (op ⦋0⦌) (ComposableArrows.mk₀ (shortestPath i j hij)) := by
  let E := constantHomEquiv (nerve (SimplicialThickening.Path i j)) B
  have hf : f.app n γ = E f (simplexComponent _ n γ) := by
    exact (congrArg (fun g ↦ g.app n γ) (E.symm_apply_apply f)).symm
  rw [hf, simplex_component_eq_shortest i j hij]
  exact constantHomEquiv_mk _ B f _

include hij in
theorem map_vertex_eq {B : Type u}
    (f : nerve (SimplicialThickening.Path i j) ⟶ constSSet B)
    (P Q : SimplicialThickening.Path i j) :
    f.app (op ⦋0⦌) (ComposableArrows.mk₀ P) =
      f.app (op ⦋0⦌) (ComposableArrows.mk₀ Q) := by
  exact (map_eq_shortest i j hij f _ _).trans
    (map_eq_shortest i j hij f _ _).symm

end
end DaggerActualConstantPathEvaluation
