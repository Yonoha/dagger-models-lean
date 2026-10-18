import OriginalNonfinalHornTerminalKan
import TopCatModelCategory.SSet.Fiber
import Mathlib.CategoryTheory.LiftingProperties.Limits

/-!
# The actual left mapping space of the original simplicial set

For vertices x and y, take the strict native fiber at y of the original
vertex-coslice suffix projection. Its n-simplices are original (n+1)-simplices
with initial vertex x and literally constant suffix y. This strict fiber is
Kan for an inner-horn-filling input, by pullback of the existing nonfinal horn
lifting and the terminal-base Kan theorem. No Kan or outer-horn hypothesis
is imposed on the original input.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial
open DaggerOriginalSimplexCoslice DaggerOriginalInnerHornFillers
open DaggerOriginalVertexCosliceLeftLifting DaggerOriginalNonfinalHornTerminalKan

universe u

namespace DaggerOriginalQuasicategoryLeftMappingSpace

noncomputable section

/-- The strict fiber over y of the original vertex-coslice suffix projection. -/
def leftMappingSubcomplex (X : SSet.{u}) (x y : X.obj (op ⦋0⦌)) :
    (simplexCoslice ⦋0⦌ X x).Subcomplex :=
  SSet.Subcomplex.fiber (cosliceProjection ⦋0⦌ X x) y

/-- The standard left mapping space, using actual original simplices and a constant suffix. -/
def leftMappingSpace (X : SSet.{u}) (x y : X.obj (op ⦋0⦌)) : SSet.{u} :=
  (leftMappingSubcomplex X x y : SSet.{u})

/-- Membership requires equality of the entire suffix with the constant simplex at y. -/
theorem mem_leftMappingSubcomplex_iff (X : SSet.{u}) (x y : X.obj (op ⦋0⦌))
    (n : SimplexCategory) (s : (simplexCoslice ⦋0⦌ X x).obj (op n)) :
    s ∈ (leftMappingSubcomplex X x y).obj (op n) ↔
      (cosliceProjection ⦋0⦌ X x).app (op n) s = X.map (n.const ⦋0⦌ 0).op y :=
  SSet.Subcomplex.mem_fiber_obj_iff _ _ _

/-- The mapping space is the literal pullback of the original projection along the vertex y. -/
theorem leftMappingSpace_isPullback (X : SSet.{u}) (x y : X.obj (op ⦋0⦌)) :
    IsPullback (leftMappingSubcomplex X x y).ι
      (SSet.stdSimplex.objZeroIsTerminal.from (leftMappingSpace X x y))
      (cosliceProjection ⦋0⦌ X x) (SSet.yonedaEquiv.symm y) :=
  SSet.Subcomplex.fiber_isPullback _ _

/-- Every original nonfinal horn lifts through the mapping-space map to the terminal simplex. -/
theorem leftMappingSpace_nonfinal_lifting {X : SSet.{u}} (hX : innerHornFillers X)
    (x y : X.obj (op ⦋0⦌)) (n : ℕ) (i : Fin (n + 2)) (hi : i < Fin.last (n + 1)) :
    HasLiftingProperty (Λ[n + 1, i] : (Δ[n + 1] : SSet.{u}).Subcomplex).ι
      (SSet.stdSimplex.objZeroIsTerminal.from (leftMappingSpace X x y)) := by
  haveI := vertex_coslice_projection_hasLiftingProperty hX n i hi x
  exact (leftMappingSpace_isPullback X x y).hasLiftingProperty _

/-- The actual standard left mapping space is Kan in arbitrary universe. -/
theorem leftMappingSpace_kan {X : SSet.{u}} (hX : innerHornFillers X)
    (x y : X.obj (op ⦋0⦌)) : (leftMappingSpace X x y).KanComplex :=
  kan_of_nonfinal_lifting_over_terminal
    (SSet.stdSimplex.objZeroIsTerminal.from (leftMappingSpace X x y))
    SSet.stdSimplex.objZeroIsTerminal
    (fun n i hi ↦ leftMappingSpace_nonfinal_lifting hX x y n i hi)

end

end DaggerOriginalQuasicategoryLeftMappingSpace
