import OriginalSingularPathTargetNaturality

/-!
# Original path-fiber naturality with explicit endpoint labels

The original maps on strict endpoint fibers and continuous path spaces are given by the same
actual postcomposition, with proofs that the original source labels map to the prescribed
original target labels. Relabelling does not replace the original spaces or maps. The existing
singular strict-fiber isomorphism is natural for every such original bipointed topological map.
-/

set_option autoImplicit false

open CategoryTheory MonoidalCategory Opposite Simplicial
open DaggerOriginalFullVertexSubcomplex DaggerOriginalContinuousEndpointCylinderFamilies
open DaggerOriginalSingularStrictContinuousPathIso DaggerOriginalSingularPathTargetNaturality

universe u

namespace DaggerOriginalLabeledPathFiberNaturality

noncomputable section

/-- The actual original strict path-fiber map, retaining explicitly prescribed endpoint labels.
-/
def labeledStrictPathFiberMap {A B : SSet.{u}} (f : A ⟶ B)
    (a b : A.obj (op ⦋0⦌)) (a' b' : B.obj (op ⦋0⦌))
    (ha : f.app (op ⦋0⦌) a = a') (hb : f.app (op ⦋0⦌) b = b') :
    (strictPathFiber A a b : SSet) ⟶ (strictPathFiber B a' b' : SSet) :=
  SSet.Subcomplex.lift ((strictPathFiber A a b).ι ≫ (ihom Δ[1]).map f) (by
    dsimp only [strictPathFiber]
    rw [SSet.Subcomplex.range_le_fiber_iff, Category.assoc, pathEv_pair_natural,
      ← Category.assoc, SSet.Subcomplex.fiber_ι_comp, SSet.const_comp]
    change SSet.const (Y := B ⊗ B) (f.app (op ⦋0⦌) a, f.app (op ⦋0⦌) b) =
      SSet.const (Y := B ⊗ B) (a', b')
    rw [ha, hb])

/-- The labelled strict-fiber map is the same original internal-hom postcomposition. -/
@[reassoc]
theorem labeledStrictPathFiberMap_ι {A B : SSet.{u}} (f : A ⟶ B)
    (a b : A.obj (op ⦋0⦌)) (a' b' : B.obj (op ⦋0⦌))
    (ha : f.app (op ⦋0⦌) a = a') (hb : f.app (op ⦋0⦌) b = b') :
    labeledStrictPathFiberMap f a b a' b' ha hb ≫ (strictPathFiber B a' b').ι =
      (strictPathFiber A a b).ι ≫ (ihom Δ[1]).map f :=
  SSet.Subcomplex.lift_ι _ _

/-- At the actual image labels this is exactly the existing original strict path-fiber map. -/
theorem labeledStrictPathFiberMap_image {A B : SSet.{u}} (f : A ⟶ B)
    (a b : A.obj (op ⦋0⦌)) :
    labeledStrictPathFiberMap f a b (f.app (op ⦋0⦌) a) (f.app (op ⦋0⦌) b) rfl rfl =
      strictPathFiberMap f a b := rfl

/-- The same actual continuous postcomposition, with prescribed original endpoint labels. -/
def labeledContinuousPathTopMap {T U : TopCat.{u}} (k : T ⟶ U) (a b : T) (a' b' : U)
    (ha : k a = a') (hb : k b = b') : continuousPathTop T a b ⟶ continuousPathTop U a' b' :=
  TopCat.ofHom
    { toFun p :=
        { toContinuousMap := k.hom.comp p.toContinuousMap
          source' := (congrArg k p.source).trans ha
          target' := (congrArg k p.target).trans hb }
      continuous_toFun := by
        apply continuous_induced_rng.mpr
        exact (ContinuousMap.continuous_postcomp k.hom).comp continuous_induced_dom }

/-- At actual image labels, this is precisely the same original continuous path postcomposition.
-/
theorem labeledContinuousPathTopMap_image {T U : TopCat.{u}} (k : T ⟶ U) (a b : T) :
    labeledContinuousPathTopMap k a b (k a) (k b) rfl rfl = continuousPathTopMap k a b := rfl

/-- The original singular endpoint labels determine the same bipointed continuous path map. -/
def labeledSingularEndpointPathTopMap {T U : TopCat.{u}} (k : T ⟶ U)
    (a b : (TopCat.toSSet.obj T).obj (op ⦋0⦌))
    (a' b' : (TopCat.toSSet.obj U).obj (op ⦋0⦌))
    (ha : (TopCat.toSSet.map k).app (op ⦋0⦌) a = a')
    (hb : (TopCat.toSSet.map k).app (op ⦋0⦌) b = b') :
    continuousPathTop T (TopCat.toSSetObj₀Equiv a) (TopCat.toSSetObj₀Equiv b) ⟶
      continuousPathTop U (TopCat.toSSetObj₀Equiv a') (TopCat.toSSetObj₀Equiv b') :=
  labeledContinuousPathTopMap k (TopCat.toSSetObj₀Equiv a) (TopCat.toSSetObj₀Equiv b)
    (TopCat.toSSetObj₀Equiv a') (TopCat.toSSetObj₀Equiv b')
    (by rw [← singularPoint_map, ha]) (by rw [← singularPoint_map, hb])

/-- The actual original singular strict-fiber isomorphism is natural for these bipointed maps.
-/
theorem singularStrictContinuousPathIso_labeled_naturality {T U : TopCat.{u}} (k : T ⟶ U)
    (a b : (TopCat.toSSet.obj T).obj (op ⦋0⦌))
    (a' b' : (TopCat.toSSet.obj U).obj (op ⦋0⦌))
    (ha : (TopCat.toSSet.map k).app (op ⦋0⦌) a = a')
    (hb : (TopCat.toSSet.map k).app (op ⦋0⦌) b = b') :
    labeledStrictPathFiberMap (TopCat.toSSet.map k) a b a' b' ha hb ≫
      (singularStrictContinuousPathIso U a' b').hom =
    (singularStrictContinuousPathIso T a b).hom ≫
      TopCat.toSSet.map (labeledSingularEndpointPathTopMap k a b a' b' ha hb) := by
  subst a'
  subst b'
  change strictPathFiberMap (TopCat.toSSet.map k) a b ≫
      (singularStrictContinuousPathIso U
        ((TopCat.toSSet.map k).app (op ⦋0⦌) a)
        ((TopCat.toSSet.map k).app (op ⦋0⦌) b)).hom =
    (singularStrictContinuousPathIso T a b).hom ≫
      TopCat.toSSet.map (continuousPathTopMap k (TopCat.toSSetObj₀Equiv a)
        (TopCat.toSSetObj₀Equiv b))
  exact singularStrictContinuousPathIso_target_naturality k a b

end

end DaggerOriginalLabeledPathFiberNaturality
