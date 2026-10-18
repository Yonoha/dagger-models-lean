import OriginalFixedObjectGroupoidHomPathFactorization

/-!
# Homotopy of the two endpoints of an actual simplicial path map

The native closed monoidal adjunction turns a full map into the interval
internal Hom into a native simplicial homotopy, retaining its exact endpoints.
-/

set_option autoImplicit false
open CategoryTheory MonoidalCategory MonoidalClosed Simplicial
open DaggerOriginalFixedObjectCotensorPoints DaggerOriginalFixedObjectGroupoidInterval
universe u

namespace DaggerOriginalSimplicialPathHomotopy

noncomputable section

/-- The two endpoint maps of any full interval internal-Hom map are simplicially homotopic. -/
def endpointHomotopy {X Y : SSet.{u}} (F : X ⟶ (ihom Δ[1]).obj Y) :
    SSet.Homotopy (F ≫ pointEvaluation (intervalPoint 0) Y)
      (F ≫ pointEvaluation (intervalPoint 1) Y) where
  h := (β_ X Δ[1]).hom ≫ uncurry F
  h₀ := by
    apply NatTrans.ext
    funext n x
    rfl
  h₁ := by
    apply NatTrans.ext
    funext n x
    rfl

  rel := by
    apply NatTrans.ext
    funext n p
    exact False.elim p.1.property

end

end DaggerOriginalSimplicialPathHomotopy
