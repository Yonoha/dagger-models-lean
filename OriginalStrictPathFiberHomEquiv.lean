import OriginalSingularEndpointCylinderAdjunction

/-!
# Maps to the actual original strict endpoint fiber

For every original simplicial parameter, maps to the actual strict endpoint fiber are exactly
maps to the original path object with both original constant endpoint equations. Applying the
native cylinder adjunction gives a concrete equivalence in every degree with the corresponding
original realized endpoint cylinders. Naturality and assembly into a simplicial isomorphism
with singular of the continuous path space are separate requirements.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial MonoidalCategory CartesianMonoidalCategory
open DaggerOriginalFullVertexSubcomplex DaggerOriginalSingularEndpointCylinderAdjunction

universe u

namespace DaggerOriginalStrictPathFiberHomEquiv

noncomputable section

/-- The paired original endpoint equation is precisely the same two constant endpoint equations.
-/
theorem paired_endpoint_eq_iff {A X : SSet.{u}} (q : A ⟶ X.path)
    (a b : X.obj (op ⦋0⦌)) :
    q ≫ X.pathEv₀₁ = SSet.const (a, b) ↔
      q ≫ X.pathEv₀ = SSet.const a ∧ q ≫ X.pathEv₁ = SSet.const b := by
  constructor
  · intro h
    constructor
    · have h₀ := congrArg (fun k ↦ k ≫ fst X X) h
      simpa only [Category.assoc, SSet.pathEv₀₁_fst, SSet.const_comp] using h₀
    · have h₁ := congrArg (fun k ↦ k ≫ snd X X) h
      simpa only [Category.assoc, SSet.pathEv₀₁_snd, SSet.const_comp] using h₁
  · rintro ⟨h₀, h₁⟩
    apply CartesianMonoidalCategory.hom_ext
    · simpa only [Category.assoc, SSet.pathEv₀₁_fst, SSet.const_comp] using h₀
    · simpa only [Category.assoc, SSet.pathEv₀₁_snd, SSet.const_comp] using h₁

/-- Maps into the actual strict endpoint fiber retain the exact original endpoint equations. -/
def strictPathFiberHomEquiv (X A : SSet.{u}) (a b : X.obj (op ⦋0⦌)) :
    (A ⟶ (strictPathFiber X a b : SSet)) ≃
      {q : A ⟶ X.path // q ≫ X.pathEv₀ = SSet.const a ∧ q ≫ X.pathEv₁ = SSet.const b} where
  toFun p := ⟨p ≫ (strictPathFiber X a b).ι, by
    apply (paired_endpoint_eq_iff _ a b).mp
    rw [Category.assoc]
    change p ≫ (SSet.Subcomplex.fiber X.pathEv₀₁ (a, b)).ι ≫ X.pathEv₀₁ = _
    rw [SSet.Subcomplex.fiber_ι_comp, SSet.comp_const]⟩
  invFun q :=
    { app n s := ⟨q.val.app n s, by
        apply (SSet.Subcomplex.mem_fiber_obj_iff X.pathEv₀₁ (a, b) _).mpr
        exact congrFun (NatTrans.congr_app ((paired_endpoint_eq_iff q.val a b).mpr
          q.property) n) s⟩
      naturality n m f := by
        ext s
        apply Subtype.ext
        exact congrFun (q.val.naturality f) s }
  left_inv p := by
    ext n s
    rfl
  right_inv q := by
    apply Subtype.ext
    ext n s
    rfl

/-- For every original simplicial parameter, maps into the actual singular endpoint fiber are
 actual original realized cylinders with exactly the corresponding endpoint restrictions. -/
def singularStrictFiberHomCylinderEquiv (T : TopCat.{u}) (A : SSet.{u})
    (a b : (TopCat.toSSet.obj T).obj (op ⦋0⦌)) :
    (A ⟶ (strictPathFiber (TopCat.toSSet.obj T) a b : SSet)) ≃
    {h : SSet.toTop.obj A ⊗ TopCat.I ⟶ T //
      TopCat.ι₀ ≫ h = (sSetTopAdj.homEquiv A T).symm (SSet.const a) ∧
      TopCat.ι₁ ≫ h = (sSetTopAdj.homEquiv A T).symm (SSet.const b)} :=
  (strictPathFiberHomEquiv (TopCat.toSSet.obj T) A a b).trans
    (singularEndpointHomCylinderEquiv T A (SSet.const a) (SSet.const b))

/-- In every degree, the actual original singular fiber simplices are the same endpoint cylinders.
-/
def singularStrictFiberSimplexCylinderEquiv (T : TopCat.{u}) (n : SimplexCategory)
    (a b : (TopCat.toSSet.obj T).obj (op ⦋0⦌)) :
    (strictPathFiber (TopCat.toSSet.obj T) a b : SSet).obj (op n) ≃
    {h : SSet.toTop.obj (SSet.stdSimplex.obj n) ⊗ TopCat.I ⟶ T //
      TopCat.ι₀ ≫ h = (sSetTopAdj.homEquiv (SSet.stdSimplex.obj n) T).symm (SSet.const a) ∧
      TopCat.ι₁ ≫ h = (sSetTopAdj.homEquiv (SSet.stdSimplex.obj n) T).symm (SSet.const b)} :=
  SSet.yonedaEquiv.symm.trans
    (singularStrictFiberHomCylinderEquiv T (SSet.stdSimplex.obj n) a b)

end

end DaggerOriginalStrictPathFiberHomEquiv
