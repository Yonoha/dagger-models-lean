import RigidificationCofBase

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

universe u

namespace DaggerOrdinaryRigidificationCof

noncomputable section

open DaggerModels.OrdinaryRigidification.NerveVertices

/-- Literal boundary zero has no simplex in any degree. -/
theorem boundary_zero_empty (q : SimplexCategoryᵒᵖ)
    (s : (SSet.boundary.{u} 0).obj q) : False := by
  apply s.property
  intro i
  exact ⟨0, (Fin.eq_zero _).trans (Fin.eq_zero i).symm⟩

theorem boundary_zero_bot : SSet.boundary.{u} 0 = ⊥ := by
  apply le_antisymm
  · intro q s hs
    exact boundary_zero_empty q ⟨s, hs⟩
  · exact bot_le

/-- Surjectivity alone lifts the SAME original dimension-zero nerve square. -/
def zeroLift {A B : SC.{u}} (p : A ⟶ B) (hp : Function.Surjective p.obj)
    {a : (SSet.boundary 0).toSSet ⟶ N.obj A}
    {b : SSet.stdSimplex.obj ⦋0⦌ ⟶ N.obj B}
    (sq : CommSq a (SSet.boundary 0).ι (N.map p) b) : sq.LiftStruct := by
  let v := SSet.yonedaEquiv b
  let c := Classical.choose (hp (vertexEquiv B v))
  have hc := Classical.choose_spec (hp (vertexEquiv B v))
  refine { l := SSet.yonedaEquiv.symm ((vertexEquiv A).symm c)
           fac_left := ?_
           fac_right := ?_ }
  · apply NatTrans.ext
    funext q s
    exact (boundary_zero_empty q s).elim
  · apply SSet.yonedaEquiv.injective
    rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply]
    apply (vertexEquiv B).injective
    rw [vertexEquiv_naturality, Equiv.apply_symm_apply]
    exact hc

theorem boundary_zero_lifting {A B : SC.{u}} (p : A ⟶ B)
    (hp : Function.Surjective p.obj) :
    HasLiftingProperty (SSet.boundary 0).ι (N.map p) :=
  ⟨fun sq => CommSq.HasLift.mk' (zeroLift p hp sq)⟩

end

end DaggerOrdinaryRigidificationCof
