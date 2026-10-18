import OriginalFullVertexSubcomplexUniversal
import TopCatModelCategory.SSet.HomotopyGroup

/-!
# Original positive-dimensional pointed simplices in a full vertex subcomplex

Every vertex of a positive-dimensional pointed simplex is its original
basepoint. The native full-subcomplex universal property therefore gives
unique factorization. The original inclusion induces a bijection on the
actual pointed simplices, retaining the map and every boundary equation.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial
open DaggerOriginalFullVertexSubcomplex

universe u

namespace DaggerOriginalFullVertexPointedSimplexComparison

noncomputable section

/-- Every vertex of a positive-dimensional pointed simplex is the same original basepoint. -/
theorem pointedSimplex_vertex {X : SSet.{u}} {x : X _⦋0⦌} {n : ℕ}
    (p : X.PtSimplex (n + 1) x) (w : (Δ[n + 1] : SSet.{u}) _⦋0⦌) :
    p.map.app (op ⦋0⦌) w = x := by
  have : (Δ[0] : SSet.{u}).HasDimensionLT (n + 1) :=
    SSet.hasDimensionLT_of_le _ 1 _ (by omega)
  have h := p.comp_map_eq_const (SSet.yonedaEquiv.symm w)
  have h' := congrArg SSet.yonedaEquiv h
  simpa using h'

variable {X : SSet.{u}} (V : Set (X _⦋0⦌))
variable (a : (fullVertexSubcomplex X V : SSet.{u}) _⦋0⦌)

/-- The actual ambient positive pointed simplex factors through the original full subcomplex. -/
def pointedSimplexLift {n : ℕ} (p : X.PtSimplex (n + 1) a.val) :
    (fullVertexSubcomplex X V : SSet.{u}).PtSimplex (n + 1) a :=
  SSet.PtSimplex.mk (liftMapOfVertices V p.map (by
    intro w
    rw [pointedSimplex_vertex]
    have h := a.property (𝟙 ⦋0⦌)
    simpa using h)) (by
      intro i
      apply (cancel_mono (fullVertexSubcomplex X V).ι).mp
      rw [Category.assoc, liftMapOfVertices_ι, p.δ_map, SSet.const_comp]
      rfl)

/-- Inclusion of the lift retains exactly the original ambient pointed simplex. -/
theorem pointedSimplexLift_pushforward {n : ℕ} (p : X.PtSimplex (n + 1) a.val) :
    (pointedSimplexLift V a p).pushforward (fullVertexSubcomplex X V).ι a.val rfl = p := by
  apply SSet.Subcomplex.RelativeMorphism.ext
  simp [pointedSimplexLift]

/-- Inclusion is injective on the original pointed simplex maps. -/
theorem pointedSimplex_pushforward_injective (n : ℕ) :
    Function.Injective (fun p : (fullVertexSubcomplex X V : SSet.{u}).PtSimplex n a ↦
      p.pushforward (fullVertexSubcomplex X V).ι a.val rfl) := by
  intro p q h
  apply SSet.Subcomplex.RelativeMorphism.ext
  apply (cancel_mono (fullVertexSubcomplex X V).ι).mp
  exact congrArg SSet.Subcomplex.RelativeMorphism.map h

/-- The original inclusion is bijective on positive-dimensional pointed simplices. -/
theorem pointedSimplex_pushforward_bijective (n : ℕ) :
    Function.Bijective (fun p : (fullVertexSubcomplex X V : SSet.{u}).PtSimplex (n + 1) a ↦
      p.pushforward (fullVertexSubcomplex X V).ι a.val rfl) :=
  ⟨pointedSimplex_pushforward_injective V a _, fun p ↦
    ⟨pointedSimplexLift V a p, pointedSimplexLift_pushforward V a p⟩⟩

end

end DaggerOriginalFullVertexPointedSimplexComparison
