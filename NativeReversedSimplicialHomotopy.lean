import NativeStandardSimplexContraction

/-!
# Raw simplicial homotopies under reversal

Reversal of the interval also reverses the two endpoints. The construction uses
the actual native simplex-category reversal on the full interval simplex.
-/
set_option autoImplicit false
open CategoryTheory Simplicial Opposite MonoidalCategory
universe u
namespace DaggerNativeReversedSimplicialHomotopy
noncomputable section

/-- Reverse both the parameter ordinal and its interval values. -/
def reverseParameter (n : SimplexCategoryᵒᵖ) (t : (Δ[1] : SSet.{u}).obj n) :
    (Δ[1] : SSet.{u}).obj n :=
  SSet.stdSimplex.objEquiv.symm (SimplexCategory.rev.map (SSet.stdSimplex.objEquiv t))

/-- The interval map respects reversed, rather than unchanged, simplex operators. -/
theorem reverseParameter_natural {n m : SimplexCategoryᵒᵖ} (i : n ⟶ m)
    (t : (Δ[1] : SSet.{u}).obj n) :
    reverseParameter m (Δ[1].map i t) =
      Δ[1].map (SimplexCategory.rev.map i.unop).op (reverseParameter n t) := by
  apply SSet.stdSimplex.objEquiv.injective
  change SimplexCategory.rev.map (i.unop ≫ SSet.stdSimplex.objEquiv t) =
    SimplexCategory.rev.map i.unop ≫ SimplexCategory.rev.map (SSet.stdSimplex.objEquiv t)
  exact SimplexCategory.rev.map_comp _ _

/-- The initial interval simplex becomes the final interval simplex in every degree. -/
theorem reverseParameter_zero {X : SSet.{u}} (n : SimplexCategoryᵒᵖ) (x : X.obj n) :
    reverseParameter n ((SSet.ι₀ (X := X)).app n x).2 =
      ((SSet.ι₁ (X := X)).app n x).2 := by
  apply SSet.stdSimplex.objEquiv.injective
  ext i
  rfl

/-- The final interval simplex becomes the initial interval simplex in every degree. -/
theorem reverseParameter_one {X : SSet.{u}} (n : SimplexCategoryᵒᵖ) (x : X.obj n) :
    reverseParameter n ((SSet.ι₁ (X := X)).app n x).2 =
      ((SSet.ι₀ (X := X)).app n x).2 := by
  apply SSet.stdSimplex.objEquiv.injective
  ext i
  rfl

/-- Reverse the actual full cylinder map, including the interval parameter. -/
def reversedCylinder {X Y : SSet.{u}} {f g : X ⟶ Y} (h : SSet.Homotopy f g) :
    X.op ⊗ Δ[1] ⟶ Y.op where
  app n p := h.h.app n (p.1, reverseParameter n p.2)
  naturality n m i := by
    cases n with
    | op n =>
      cases m with
      | op m =>
        induction n using SimplexCategory.rec with
        | h a =>
          induction m using SimplexCategory.rec with
          | h b =>
            funext p
            change h.h.app _
              (X.map (SimplexCategory.rev.map i.unop).op p.1,
                reverseParameter _ (Δ[1].map i p.2)) =
              Y.map (SimplexCategory.rev.map i.unop).op
                (h.h.app _ (p.1, reverseParameter _ p.2))
            rw [reverseParameter_natural]
            exact congrFun (h.h.naturality (SimplexCategory.rev.map i.unop).op)
              (p.1, reverseParameter _ p.2)

/-- Actual reversal sends a raw homotopy to a homotopy with the endpoints interchanged. -/
def reversedHomotopy {X Y : SSet.{u}} {f g : X ⟶ Y} (h : SSet.Homotopy f g) :
    SSet.Homotopy (SSet.opFunctor.map g) (SSet.opFunctor.map f) :=
  SSet.Homotopy.mk (reversedCylinder h) (by
    ext n x
    change h.h.app n (x, reverseParameter n ((SSet.ι₀ (X := X)).app n x).2) = g.app n x
    rw [reverseParameter_zero]
    exact congrFun (NatTrans.congr_app h.h₁ n) x) (by
    ext n x
    change h.h.app n (x, reverseParameter n ((SSet.ι₁ (X := X)).app n x).2) = f.app n x
    rw [reverseParameter_one]
    exact congrFun (NatTrans.congr_app h.h₀ n) x)

end
end DaggerNativeReversedSimplicialHomotopy
