import OriginalRelativeLeftOneHornEdges

/-!
# Original invertible edges lifted with a prescribed target

Lift the original reverse edge from the prescribed source vertex using the
native relative (1,0)-horn. Lift its inverse triangle with the native relative
(2,0)-horn. The resulting edge ends at the prescribed vertex and has the exact
original base one-simplex as image. Original invertibility is reflected by the
already proved relative two-horn theorem. No source Kan premise is introduced.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial
open DaggerOriginalOrdinaryKanCoreEdgeMembership
open DaggerOriginalInnerHornFillers
open DaggerOriginalQuasicategoryInvertibleTriangles
open DaggerOriginalRelativeLeftTwoHornInverses
open DaggerOriginalRelativeLeftOneHornEdges

universe u

namespace DaggerOriginalRelativeInvertibleEdgeTargetLift

noncomputable section

/-- Lift an invertible original base edge to its prescribed target, retaining its exact image.
-/
theorem lift_invertible_edge_to_target {E X : SSet.{u}} (p : E ⟶ X)
    [HasLiftingProperty (Λ[1, 0] : (Δ[1] : SSet.{u}).Subcomplex).ι p]
    [HasLiftingProperty (Λ[2, 0] : (Δ[2] : SSet.{u}).Subcomplex).ι p]
    (hX : innerHornFillers X) (b : E.obj (op ⦋0⦌)) {x : X.obj (op ⦋0⦌)}
    (e : SSet.Edge x (p.app (op ⦋0⦌) b)) (he : edgeIsInvertible X e.edge) :
    ∃ a : E.obj (op ⦋0⦌), p.app (op ⦋0⦌) a = x ∧
      ∃ g : SSet.Edge a b, p.app (op ⦋1⦌) g.edge = e.edge ∧
        edgeIsInvertible E g.edge := by
  obtain ⟨r, _, ⟨t⟩, _⟩ := inverse_triangles hX e he
  obtain ⟨a, ha, q, hqp⟩ := lift_edge_from_source p b r
  subst x
  have hqr : q.map p = r := SSet.Edge.ext hqp
  have t' : (q.map p).CompStruct e ((SSet.Edge.id b).map p) := by
    simpa only [hqr, SSet.Edge.map_id] using t
  obtain ⟨g, _, hgp⟩ := lift_inverse_triangle p q e t'
  have hgimage : edgeIsInvertible X (g.map p).edge := by
    rw [hgp]
    exact he
  exact ⟨a, rfl, g, congrArg SSet.Edge.edge hgp,
    edgeIsInvertible_of_invertible_image p hX g hgimage⟩

end

end DaggerOriginalRelativeInvertibleEdgeTargetLift
