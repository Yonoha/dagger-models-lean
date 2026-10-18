import OriginalQuasicategoryComposeEdges

/-!
# Every original homotopy-category arrow is represented by an actual edge

Use the original path-quotient homotopy category. Its native universal property
for multiplicative morphism properties reduces representability to identities
and composition. Actual inner two-horn fillers supply the composition triangles.
All endpoints are the original vertices, in arbitrary universe.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial
open DaggerOriginalInnerHornFillers
open DaggerOriginalQuasicategoryComposeEdges

universe u

namespace DaggerOriginalQuasicategoryPathEdgeRepresentatives

noncomputable section

/-- Original path-quotient arrows which are the class of an actual edge with these endpoints. -/
def representedByEdge (X : SSet.{u}) :
    MorphismProperty ((SSet.truncation 2).obj X).HomotopyCategory :=
  fun x y f ↦ ∃ e : SSet.Edge (X := X) x.as.as y.as.as,
    SSet.Truncated.HomotopyCategory.homMk e = f

/-- Literal inner-horn fillers make edge representability multiplicative in the original ho(X). -/
theorem representedByEdge_isMultiplicative (X : SSet.{u}) (hX : innerHornFillers X) :
    (representedByEdge X).IsMultiplicative where
  id_mem x := by
    refine ⟨SSet.Edge.id x.as.as, ?_⟩
    exact SSet.Truncated.HomotopyCategory.homMk_id _
  comp_mem f g hf hg := by
    obtain ⟨e, rfl⟩ := hf
    obtain ⟨k, rfl⟩ := hg
    obtain ⟨h, ⟨t⟩⟩ := compose_edges hX e k
    exact ⟨h, (SSet.Truncated.HomotopyCategory.homMk_comp_homMk t).symm⟩

/-- Every original path-quotient arrow has an edge representative for an inner-horn input. -/
theorem representedByEdge_eq_top (X : SSet.{u}) (hX : innerHornFillers X) :
    representedByEdge X = ⊤ := by
  have : (representedByEdge X).IsMultiplicative := representedByEdge_isMultiplicative X hX
  apply SSet.Truncated.HomotopyCategory.morphismProperty_eq_top
  intro x y e
  exact ⟨e, rfl⟩

/-- Every arrow between the exact original vertices is represented by an original edge. -/
theorem original_homMk_surjective (X : SSet.{u}) (hX : innerHornFillers X)
    {x y : X.obj (op ⦋0⦌)} :
    Function.Surjective (SSet.Truncated.HomotopyCategory.homMk (V :=
      (SSet.truncation 2).obj X) : SSet.Edge x y → _) := by
  intro f
  have h : representedByEdge X f := by
    rw [representedByEdge_eq_top X hX]
    trivial
  exact h

end

end DaggerOriginalQuasicategoryPathEdgeRepresentatives
