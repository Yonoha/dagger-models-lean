import OriginalSingularConstantEndpointCylinders

/-!
# Original endpoint cylinders and continuous families of paths

The actual ordinary compact-open topology on Mathlib paths is induced by the map to continuous
interval maps. Native continuous currying and uncurrying therefore give an endpoint-preserving
hom equivalence for every original topological parameter. The interval is the same lifted native
TopCat interval used by the original realization comparison.
-/

set_option autoImplicit false

open CategoryTheory MonoidalCategory

universe u

namespace DaggerOriginalContinuousEndpointCylinderFamilies

noncomputable section

/-- The native compact-open space of paths between the same original two points. -/
def continuousPathTop (T : TopCat.{u}) (a b : T) : TopCat.{u} :=
  TopCat.of (_root_.Path a b)

/-- Actual original cylinders with both original constant endpoint restrictions. -/
def constantEndpointCylinders (E T : TopCat.{u}) (a b : T) :=
  {h : E ⊗ TopCat.I ⟶ T // TopCat.ι₀ ≫ h = TopCat.const a ∧
    TopCat.ι₁ ≫ h = TopCat.const b}

/-- The native compact-open correspondence retains both original cylinder endpoints. -/
def constantCylinderPathFamilyEquiv (E T : TopCat.{u}) (a b : T) :
    constantEndpointCylinders E T a b ≃ (E ⟶ continuousPathTop T a b) where
  toFun f := TopCat.ofHom
    { toFun e :=
        { toContinuousMap := f.val.hom.comp
            ⟨fun t ↦ (e, ULift.up t), continuous_const.prodMk continuous_uliftUp⟩
          source' := ConcreteCategory.congr_hom f.property.1 e
          target' := ConcreteCategory.congr_hom f.property.2 e }
      continuous_toFun := by
        apply continuous_induced_rng.mpr
        exact (ContinuousMap.curry (f.val.hom.comp
          ⟨fun p ↦ (p.1, ULift.up p.2),
            continuous_fst.prodMk (continuous_uliftUp.comp continuous_snd)⟩)).continuous }
  invFun g :=
    ⟨TopCat.ofHom
      ((ContinuousMap.uncurry
        ⟨fun e ↦ (g e).toContinuousMap, continuous_induced_rng.mp g.hom.continuous⟩).comp
          ⟨fun p ↦ (p.1, p.2.down),
            continuous_fst.prodMk (continuous_uliftDown.comp continuous_snd)⟩), by
      constructor
      · apply ConcreteCategory.hom_ext
        intro e
        exact (g e).source
      · apply ConcreteCategory.hom_ext
        intro e
        exact (g e).target⟩
  left_inv f := by
    apply Subtype.ext
    ext ⟨e, t⟩
    rfl
  right_inv g := by
    apply ConcreteCategory.hom_ext
    intro e
    apply Path.ext
    funext t
    rfl

/-- Currying evaluates the same original cylinder at the same original parameter and time. -/
theorem constantCylinderPathFamilyEquiv_apply (E T : TopCat.{u}) (a b : T)
    (f : constantEndpointCylinders E T a b) (e : E) (t : unitInterval) :
    (constantCylinderPathFamilyEquiv E T a b f e).toContinuousMap t = f.val (e, ULift.up t) := rfl

end

end DaggerOriginalContinuousEndpointCylinderFamilies
