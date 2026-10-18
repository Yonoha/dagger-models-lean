import RigidificationCofExtensionFaces
import RigidificationCofZero

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

universe u

namespace DaggerOrdinaryRigidificationCof

noncomputable section

open BoundaryData PathFacets

/-- The actual enriched extension supplies BOTH triangles of the original nerve square. -/
def positiveLift {A B : SC.{u}} (p : A ⟶ B) (hp : ordinaryTrivialFibrations p) (n : ℕ)
    {a : (SSet.boundary (n + 1)).toSSet ⟶ N.obj A}
    {b : SSet.stdSimplex.obj ⦋n + 1⦌ ⟶ N.obj B}
    (sq : CommSq a (SSet.boundary (n + 1)).ι (N.map p) b) : sq.LiftStruct := by
  let d := scalarLift a b p sq hp
  let H := extensionFunctor a d.l d.fac_left
  refine { l := SSet.yonedaEquiv.symm (ULift.up H)
           fac_left := ?_
           fac_right := ?_ }
  · apply NatTrans.ext
    funext q s
    apply ULift.ext
    let φ : q.unop ⟶ ⦋n + 1⦌ := SSet.stdSimplex.objEquiv s.val
    change T.map φ ≫ H = (a.app q s).down
    have h := extensionFunctor_on_simplex a d.l d.fac_left φ s.property
    have hs : (⟨SSet.stdSimplex.objEquiv.symm φ, s.property⟩ :
        (SSet.boundary (n + 1)).toSSet.obj q) = s :=
      Subtype.ext (SSet.stdSimplex.objEquiv.symm_apply_apply s.val)
    exact h.trans (congrArg (fun t => (a.app q t).down) hs)
  · apply SSet.yonedaEquiv.injective
    rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply]
    apply ULift.ext
    change H ≫ p = top b
    exact extensionFunctor_over a d.l d.fac_left b p sq d.fac_right

/-- Every boundary, INCLUDING zero, lifts against the SAME original coherent nerve map. -/
theorem boundary_lifting {A B : SC.{u}} (p : A ⟶ B) (hp : ordinaryTrivialFibrations p)
    (n : ℕ) : HasLiftingProperty (SSet.boundary n).ι (N.map p) := by
  cases n with
  | zero => exact boundary_zero_lifting p hp.1
  | succ n => exact ⟨fun sq => CommSq.HasLift.mk' (positiveLift p hp n sq)⟩

end

end DaggerOrdinaryRigidificationCof
