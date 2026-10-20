import OriginalDaggerRealizationC2Action
import Mathlib.CategoryTheory.CodiscreteCategory
import Mathlib.AlgebraicTopology.SimplicialSet.Nerve

/-!
# The actual simplicial regular action on the codiscrete nerve

This is the manuscript's simplicial `E_• C₂`. The topological free and
contractible `EC₂` is a later theorem, not part of this construction.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial
open DaggerOriginalDaggerRealizationC2Action

universe u

namespace DaggerOriginalEC2SimplicialAction

noncomputable section

/-- The regular left action of the previously chosen actual two-element group. -/
def regularAction : Action (Type u) C2.{u} where
  V := C2.{u}
  ρ :=
    { toFun := fun g ↦ End.of (fun x : C2.{u} ↦ g * x)
      map_one' := by
        apply End.ext
        funext x
        exact one_mul x
      map_mul' := by
        intro g h
        apply End.ext
        funext x
        exact mul_assoc g h x }

/-- The codiscrete category on the literal acting group, followed by its nerve. -/
private def codiscreteNerve : Type u ⥤ SSet.{u} :=
  Codiscrete.functorToCat ⋙ nerveFunctor

/-- The manuscript's actual simplicial $E_\bullet C_2$. -/
def simplicialEC2 : SSet.{u} := nerve (Codiscrete C2.{u})

/-- Transport the regular action functorially through codiscrete category and nerve. -/
def simplicialAction : Action SSet.{u} C2.{u} :=
  (codiscreteNerve.{u}.mapAction C2.{u}).obj regularAction.{u}

/-- The acting simplicial set is definitionally the original codiscrete nerve. -/
theorem simplicialAction_obj : simplicialAction.{u}.V = simplicialEC2.{u} := rfl

/-- The action in degree zero is literal left multiplication on objects. -/
theorem action_vertex (g x : C2.{u}) :
    ((simplicialAction.{u}.ρ g).asHom).app (op ⦋0⦌)
        (ComposableArrows.mk₀ (Codiscrete.mk x)) =
      ComposableArrows.mk₀ (Codiscrete.mk (g * x)) := by
  change (nerveMap (Codiscrete.functorOfFun (fun z : C2.{u} ↦ g * z))).app
    (op ⦋0⦌) (ComposableArrows.mk₀ (Codiscrete.mk x)) = _
  rw [nerveMap_app_mk₀]
  rfl

/-- The action is free on actual zero-simplices, including the nonidentity element. -/
theorem action_vertex_free (g : C2.{u})
    (z : simplicialEC2.{u}.obj (op ⦋0⦌))
    (hz : ((simplicialAction.{u}.ρ g).asHom).app (op ⦋0⦌) z = z) : g = 1 := by
  let x : Codiscrete C2.{u} := nerveEquiv z
  have hrepr : z = ComposableArrows.mk₀ (Codiscrete.mk x.as) := by
    simpa only [Codiscrete.mk_as] using (nerveEquiv.left_inv z).symm
  rw [hrepr] at hz
  rw [action_vertex] at hz
  have h := congrArg (fun t : ComposableArrows (Codiscrete C2.{u}) 0 ↦
    (nerveEquiv t).as) hz
  change g * x.as = x.as at h
  have h' : g * x.as = (1 : C2.{u}) * x.as := by simpa using h
  exact mul_right_cancel h'

end

end DaggerOriginalEC2SimplicialAction
