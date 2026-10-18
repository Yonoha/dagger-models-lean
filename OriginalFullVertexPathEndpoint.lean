import OriginalFullVertexStrictEndpointCylinder
import TopCatModelCategory.SSet.Loop

/-!
# Endpoint evaluation of a simplicial cylinder

This identifies the literal internal-hom endpoint maps with evaluation of an
uncurried simplicial cylinder at the corresponding vertex. It is the bridge
between pointwise vertex factorization and strict endpoint path fibers.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial MonoidalCategory MonoidalClosed

universe u

namespace DaggerOriginalFullVertexSubcomplex

noncomputable section

theorem uncurry_path_endpoint_zero {Z X : SSet.{u}}
    (q : Z ⟶ X.path) (z : Z.obj (op ⦋0⦌)) :
    (uncurry q).app (op ⦋0⦌)
      ⟨SSet.stdSimplex.obj₀Equiv.symm 0, z⟩ =
      (q ≫ X.pathEv₀).app (op ⦋0⦌) z := by
  rfl

theorem uncurry_path_endpoint_one {Z X : SSet.{u}}
    (q : Z ⟶ X.path) (z : Z.obj (op ⦋0⦌)) :
    (uncurry q).app (op ⦋0⦌)
      ⟨SSet.stdSimplex.obj₀Equiv.symm 1, z⟩ =
      (q ≫ X.pathEv₁).app (op ⦋0⦌) z := by
  rfl

end

end DaggerOriginalFullVertexSubcomplex
