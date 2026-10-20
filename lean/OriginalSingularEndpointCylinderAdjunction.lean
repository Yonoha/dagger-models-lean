import OriginalSingularPathCylinderAdjunction

/-!
# Both original endpoints of the singular path-cylinder adjunction

For every original simplicial parameter, the original path evaluations correspond exactly to
the two original realized cylinder restrictions. The existing native realization-singular
adjunction and native one-simplex product isomorphism supply both formulas. The hom equivalence
therefore restricts to the same original endpoint equations, with arbitrary prescribed maps.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial MonoidalCategory MonoidalClosed
open DaggerOriginalSingularPathCylinderAdjunction

universe u

namespace DaggerOriginalSingularEndpointCylinderAdjunction

noncomputable section

/-- The original equivalence is exactly realization of the same uncurried simplicial cylinder. -/
theorem singularPathHomCylinderEquiv_apply (T : TopCat.{u}) (A : SSet.{u})
    (q : A ⟶ (TopCat.toSSet.obj T).path) :
    singularPathHomCylinderEquiv T A q =
      (SSet.stdSimplex.toTopTensorDeltaOneIso A).inv ≫
        (sSetTopAdj.homEquiv (A ⊗ Δ[1]) T).symm ((β_ A Δ[1]).hom ≫ uncurry q) := by
  rfl

/-- The same original zero path endpoint becomes the exact zero cylinder restriction. -/
theorem singularPathHomCylinderEquiv_source (T : TopCat.{u}) (A : SSet.{u})
    (q : A ⟶ (TopCat.toSSet.obj T).path) :
    TopCat.ι₀ ≫ singularPathHomCylinderEquiv T A q =
      (sSetTopAdj.homEquiv A T).symm (q ≫ (TopCat.toSSet.obj T).pathEv₀) := by
  rw [singularPathHomCylinderEquiv_apply,
    SSet.stdSimplex.ι₀_toTopTensorDeltaOneIso_inv_assoc,
    ← sSetTopAdj.homEquiv_naturality_left_symm]
  rfl

/-- The same original one path endpoint becomes the exact one cylinder restriction. -/
theorem singularPathHomCylinderEquiv_target (T : TopCat.{u}) (A : SSet.{u})
    (q : A ⟶ (TopCat.toSSet.obj T).path) :
    TopCat.ι₁ ≫ singularPathHomCylinderEquiv T A q =
      (sSetTopAdj.homEquiv A T).symm (q ≫ (TopCat.toSSet.obj T).pathEv₁) := by
  rw [singularPathHomCylinderEquiv_apply,
    SSet.stdSimplex.ι₁_toTopTensorDeltaOneIso_inv_assoc,
    ← sSetTopAdj.homEquiv_naturality_left_symm]
  rfl

/-- The actual hom equivalence retains both prescribed original endpoint maps simultaneously. -/
def singularEndpointHomCylinderEquiv (T : TopCat.{u}) (A : SSet.{u})
    (f g : A ⟶ TopCat.toSSet.obj T) :
    {q : A ⟶ (TopCat.toSSet.obj T).path //
      q ≫ (TopCat.toSSet.obj T).pathEv₀ = f ∧ q ≫ (TopCat.toSSet.obj T).pathEv₁ = g} ≃
    {h : SSet.toTop.obj A ⊗ TopCat.I ⟶ T //
      TopCat.ι₀ ≫ h = (sSetTopAdj.homEquiv A T).symm f ∧
      TopCat.ι₁ ≫ h = (sSetTopAdj.homEquiv A T).symm g} where
  toFun q := ⟨singularPathHomCylinderEquiv T A q.val, by
    constructor
    · rw [singularPathHomCylinderEquiv_source, q.property.1]
    · rw [singularPathHomCylinderEquiv_target, q.property.2]⟩
  invFun h := ⟨(singularPathHomCylinderEquiv T A).symm h.val, by
    constructor
    · apply (sSetTopAdj.homEquiv A T).symm.injective
      rw [← singularPathHomCylinderEquiv_source, Equiv.apply_symm_apply]
      exact h.property.1
    · apply (sSetTopAdj.homEquiv A T).symm.injective
      rw [← singularPathHomCylinderEquiv_target, Equiv.apply_symm_apply]
      exact h.property.2⟩
  left_inv q := Subtype.ext ((singularPathHomCylinderEquiv T A).symm_apply_apply q.val)
  right_inv h := Subtype.ext ((singularPathHomCylinderEquiv T A).apply_symm_apply h.val)

end

end DaggerOriginalSingularEndpointCylinderAdjunction
