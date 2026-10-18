import OriginalUnitaryStrictContinuousPathIso

/-!
# Original target-map naturality of the singular endpoint-fiber isomorphism

Continuous postcomposition acts on the same original compact-open path spaces and constant
endpoint cylinders. The native singular functor and internal-hom adjunction retain the original
endpoint images. These formulas connect postcomposition to the actual strict-fiber isomorphism,
including the concrete Yoneda reconstruction of its original hom.
-/

set_option autoImplicit false

open CategoryTheory MonoidalCategory MonoidalClosed Opposite Simplicial
open DaggerOriginalFullVertexSubcomplex DaggerOriginalContinuousEndpointCylinderFamilies
open DaggerOriginalSingularStrictContinuousPathIso DaggerOriginalSingularPathCylinderAdjunction
open DaggerOriginalSingularEndpointCylinderAdjunction

universe u

namespace DaggerOriginalSingularPathTargetNaturality

noncomputable section

/-- Continuous postcomposition on the same original compact-open path spaces. -/
def continuousPathTopMap {T U : TopCat.{u}} (k : T ⟶ U) (a b : T) :
    continuousPathTop T a b ⟶ continuousPathTop U (k a) (k b) :=
  TopCat.ofHom
    { toFun p := p.map k.hom.continuous
      continuous_toFun := by
        apply continuous_induced_rng.mpr
        exact (ContinuousMap.continuous_postcomp k.hom).comp continuous_induced_dom }

/-- Native singular vertex evaluation commutes with the same original topological target map. -/
theorem singularPoint_map {T U : TopCat.{u}} (k : T ⟶ U)
    (a : (TopCat.toSSet.obj T).obj (op ⦋0⦌)) :
    TopCat.toSSetObj₀Equiv ((TopCat.toSSet.map k).app (op ⦋0⦌) a) =
      k (TopCat.toSSetObj₀Equiv a) := rfl

/-- Postcomposition on paths with the exact original singular endpoint images. -/
def singularEndpointPathTopMap {T U : TopCat.{u}} (k : T ⟶ U)
    (a b : (TopCat.toSSet.obj T).obj (op ⦋0⦌)) :
    continuousPathTop T (TopCat.toSSetObj₀Equiv a) (TopCat.toSSetObj₀Equiv b) ⟶
      continuousPathTop U
        (TopCat.toSSetObj₀Equiv ((TopCat.toSSet.map k).app (op ⦋0⦌) a))
        (TopCat.toSSetObj₀Equiv ((TopCat.toSSet.map k).app (op ⦋0⦌) b)) :=
  continuousPathTopMap k (TopCat.toSSetObj₀Equiv a) (TopCat.toSSetObj₀Equiv b)

/-- Target postcomposition on the same original constant endpoint cylinders. -/
def constantCylinderPostcompose {E T U : TopCat.{u}} (k : T ⟶ U) {a b : T}
    (h : constantEndpointCylinders E T a b) : constantEndpointCylinders E U (k a) (k b) :=
  ⟨h.val ≫ k, by
    constructor
    · apply ConcreteCategory.hom_ext
      intro e
      exact congrArg k (ConcreteCategory.congr_hom h.property.1 e)
    · apply ConcreteCategory.hom_ext
      intro e
      exact congrArg k (ConcreteCategory.congr_hom h.property.2 e)⟩

/-- Native continuous path-family currying commutes with original target postcomposition. -/
theorem constantCylinderPathFamilyEquiv_target_naturality {E T U : TopCat.{u}}
    (k : T ⟶ U) (a b : T) (h : constantEndpointCylinders E T a b) :
    constantCylinderPathFamilyEquiv E U (k a) (k b) (constantCylinderPostcompose k h) =
      constantCylinderPathFamilyEquiv E T a b h ≫ continuousPathTopMap k a b := by
  apply ConcreteCategory.hom_ext
  intro e
  apply Path.ext
  funext t
  rfl

/-- The same original singular path hom correspondence commutes with target postcomposition. -/
theorem singularPathHomCylinderEquiv_target_naturality {T U : TopCat.{u}} (k : T ⟶ U)
    (A : SSet.{u}) (q : A ⟶ (TopCat.toSSet.obj T).path) :
    singularPathHomCylinderEquiv U A (q ≫ (ihom Δ[1]).map (TopCat.toSSet.map k)) =
      singularPathHomCylinderEquiv T A q ≫ k := by
  rw [singularPathHomCylinderEquiv_apply, singularPathHomCylinderEquiv_apply,
    uncurry_natural_right, ← Category.assoc (β_ A Δ[1]).hom,
    sSetTopAdj.homEquiv_naturality_right_symm, Category.assoc]

/-- Strict-fiber postcomposition and the same original cylinder hom correspondence commute. -/
theorem singularStrictOriginalCylinderHomEquiv_target_naturality {T U : TopCat.{u}}
    (k : T ⟶ U) (A : SSet.{u}) (a b : (TopCat.toSSet.obj T).obj (op ⦋0⦌))
    (q : A ⟶ (strictPathFiber (TopCat.toSSet.obj T) a b : SSet)) :
    singularStrictOriginalCylinderHomEquiv U A
      ((TopCat.toSSet.map k).app (op ⦋0⦌) a) ((TopCat.toSSet.map k).app (op ⦋0⦌) b)
      (q ≫ strictPathFiberMap (TopCat.toSSet.map k) a b) =
    constantCylinderPostcompose k (singularStrictOriginalCylinderHomEquiv T A a b q) := by
  apply Subtype.ext
  change singularPathHomCylinderEquiv U A
    (q ≫ strictPathFiberMap (TopCat.toSSet.map k) a b ≫
      (strictPathFiber (TopCat.toSSet.obj U)
        ((TopCat.toSSet.map k).app (op ⦋0⦌) a)
        ((TopCat.toSSet.map k).app (op ⦋0⦌) b)).ι) =
    singularPathHomCylinderEquiv T A
      (q ≫ (strictPathFiber (TopCat.toSSet.obj T) a b).ι) ≫ k
  rw [strictPathFiberMap, SSet.Subcomplex.lift_ι, ← Category.assoc,
    singularPathHomCylinderEquiv_target_naturality]

/-- The exact original strict-fiber hom equivalence is natural in the original target map. -/
theorem singularStrictContinuousPathHomEquiv_target_naturality {T U : TopCat.{u}}
    (k : T ⟶ U) (A : SSet.{u}) (a b : (TopCat.toSSet.obj T).obj (op ⦋0⦌))
    (q : A ⟶ (strictPathFiber (TopCat.toSSet.obj T) a b : SSet)) :
    singularStrictContinuousPathHomEquiv U A
      ((TopCat.toSSet.map k).app (op ⦋0⦌) a) ((TopCat.toSSet.map k).app (op ⦋0⦌) b)
      (q ≫ strictPathFiberMap (TopCat.toSSet.map k) a b) =
    singularStrictContinuousPathHomEquiv T A a b q ≫
      TopCat.toSSet.map (singularEndpointPathTopMap k a b) := by
  change (sSetTopAdj.homEquiv A _)
    (constantCylinderPathFamilyEquiv (SSet.toTop.obj A) U _ _
      (singularStrictOriginalCylinderHomEquiv U A _ _
        (q ≫ strictPathFiberMap (TopCat.toSSet.map k) a b))) =
    (sSetTopAdj.homEquiv A _)
      (constantCylinderPathFamilyEquiv (SSet.toTop.obj A) T _ _
        (singularStrictOriginalCylinderHomEquiv T A a b q)) ≫
      TopCat.toSSet.map (continuousPathTopMap k _ _)
  rw [singularStrictOriginalCylinderHomEquiv_target_naturality]
  change (sSetTopAdj.homEquiv A
    (continuousPathTop U (k (TopCat.toSSetObj₀Equiv a)) (k (TopCat.toSSetObj₀Equiv b))))
    (constantCylinderPathFamilyEquiv (SSet.toTop.obj A) U
      (k (TopCat.toSSetObj₀Equiv a)) (k (TopCat.toSSetObj₀Equiv b))
      (constantCylinderPostcompose k (singularStrictOriginalCylinderHomEquiv T A a b q))) =
    (sSetTopAdj.homEquiv A
      (continuousPathTop T (TopCat.toSSetObj₀Equiv a) (TopCat.toSSetObj₀Equiv b)))
      (constantCylinderPathFamilyEquiv (SSet.toTop.obj A) T
        (TopCat.toSSetObj₀Equiv a) (TopCat.toSSetObj₀Equiv b)
        (singularStrictOriginalCylinderHomEquiv T A a b q)) ≫
      TopCat.toSSet.map (continuousPathTopMap k (TopCat.toSSetObj₀Equiv a)
        (TopCat.toSSetObj₀Equiv b))
  rw [constantCylinderPathFamilyEquiv_target_naturality,
    sSetTopAdj.homEquiv_naturality_right]

/-- The native Yoneda reconstruction gives exactly the original hom correspondence at identity.
-/
theorem singularStrictContinuousPathIso_hom (T : TopCat.{u})
    (a b : (TopCat.toSSet.obj T).obj (op ⦋0⦌)) :
    (singularStrictContinuousPathIso T a b).hom =
      singularStrictContinuousPathHomEquiv T
        (strictPathFiber (TopCat.toSSet.obj T) a b : SSet) a b (𝟙 _) := by
  have h : yoneda.map (singularStrictContinuousPathIso T a b).hom =
      (singularStrictContinuousPathYonedaIso T a b).hom := by
    change yoneda.map (yoneda.preimage _) = _
    exact yoneda.map_preimage _
  have h₀ := congrFun (NatTrans.congr_app h
    (op (strictPathFiber (TopCat.toSSet.obj T) a b : SSet))) (𝟙 _)
  simpa only [Category.id_comp] using h₀

/-- Postcomposition by the actual isomorphism is the same original natural hom correspondence.
-/
theorem singularStrictContinuousPathIso_hom_comp (T : TopCat.{u}) (A : SSet.{u})
    (a b : (TopCat.toSSet.obj T).obj (op ⦋0⦌))
    (q : A ⟶ (strictPathFiber (TopCat.toSSet.obj T) a b : SSet)) :
    q ≫ (singularStrictContinuousPathIso T a b).hom =
      singularStrictContinuousPathHomEquiv T A a b q := by
  rw [singularStrictContinuousPathIso_hom]
  simpa only [Category.comp_id] using
    (singularStrictContinuousPathHomEquiv_parameter_naturality T q a b (𝟙 _)).symm

/-- The actual strict singular endpoint-fiber isomorphism commutes with the original target map.
-/
theorem singularStrictContinuousPathIso_target_naturality {T U : TopCat.{u}} (k : T ⟶ U)
    (a b : (TopCat.toSSet.obj T).obj (op ⦋0⦌)) :
    strictPathFiberMap (TopCat.toSSet.map k) a b ≫
      (singularStrictContinuousPathIso U
        ((TopCat.toSSet.map k).app (op ⦋0⦌) a)
        ((TopCat.toSSet.map k).app (op ⦋0⦌) b)).hom =
    (singularStrictContinuousPathIso T a b).hom ≫
      TopCat.toSSet.map (singularEndpointPathTopMap k a b) := by
  rw [singularStrictContinuousPathIso_hom_comp, singularStrictContinuousPathIso_hom]
  simpa only [Category.id_comp] using
    singularStrictContinuousPathHomEquiv_target_naturality k
      (strictPathFiber (TopCat.toSSet.obj T) a b : SSet) a b (𝟙 _)

end

end DaggerOriginalSingularPathTargetNaturality
