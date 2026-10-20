import OriginalFullVertexPathEndpoint

/-!
# The retained strict-endpoint simplicial path fiber

This uses the actual internal-hom path object and its pair of endpoint
evaluations from `TopCatModelCategory.SSet.Loop`. The comparison map is the
map induced by inclusion of a full vertex subcomplex.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial MonoidalCategory MonoidalClosed
  CartesianMonoidalCategory
open DaggerOriginalFullVertexSubcomplex

universe u

namespace DaggerOriginalFullVertexSubcomplex

noncomputable section

/-- The literal fiber of the paired endpoint evaluation map. -/
def strictPathFiber (X : SSet.{u}) (a b : X.obj (op ⦋0⦌)) :
    X.path.Subcomplex :=
  SSet.Subcomplex.fiber X.pathEv₀₁ ⟨a, b⟩

/-- Naturality of the actual paired endpoint evaluation. -/
theorem pathEv_pair_natural {A X : SSet.{u}} (i : A ⟶ X) :
    ((ihom Δ[1]).map i) ≫ X.pathEv₀₁ =
      A.pathEv₀₁ ≫ (i ⊗ₘ i) := by
  ext : 1
  · simpa only [Category.assoc, SSet.pathEv₀₁_fst,
      SSet.pathEv₀, SSet.tensorHom_app_apply] using
      ((Δ[1].ihomEv (SSet.stdSimplex.obj₀Equiv.symm 0)).naturality i)
  · simpa only [Category.assoc, SSet.pathEv₀₁_snd,
      SSet.pathEv₁, SSet.tensorHom_app_apply] using
      ((Δ[1].ihomEv (SSet.stdSimplex.obj₀Equiv.symm 1)).naturality i)

/-- A simplicial map induces a map on the strict-endpoint path fibers. -/
def strictPathFiberMap {A X : SSet.{u}} (i : A ⟶ X)
    (a b : A.obj (op ⦋0⦌)) :
    (strictPathFiber A a b : SSet) ⟶
      (strictPathFiber X (i.app (op ⦋0⦌) a) (i.app (op ⦋0⦌) b) : SSet) :=
  SSet.Subcomplex.lift
    ((strictPathFiber A a b).ι ≫ (ihom Δ[1]).map i) (by
      dsimp only [strictPathFiber]
      rw [SSet.Subcomplex.range_le_fiber_iff]
      calc
        (strictPathFiber A a b).ι ≫ (ihom Δ[1]).map i ≫ X.pathEv₀₁ =
            (strictPathFiber A a b).ι ≫ A.pathEv₀₁ ≫ (i ⊗ₘ i) := by
          rw [pathEv_pair_natural]
        _ = SSet.const (X := (strictPathFiber A a b : SSet))
              ((a, b) : (A ⊗ A : SSet.{u}) _⦋0⦌) ≫ (i ⊗ₘ i) := by
          rw [← Category.assoc]
          dsimp only [strictPathFiber]
          rw [SSet.Subcomplex.fiber_ι_comp]
        _ = SSet.const (X := (strictPathFiber A a b : SSet))
              ((i.app (op ⦋0⦌) a, i.app (op ⦋0⦌) b) :
                (X ⊗ X : SSet.{u}) _⦋0⦌) := by
          rw [SSet.const_comp]
          rfl)

end

end DaggerOriginalFullVertexSubcomplex
