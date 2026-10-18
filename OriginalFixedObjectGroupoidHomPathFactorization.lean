import OriginalFixedObjectCotensorFibrations
import TopCatModelCategory.SSet.Loop

/-!
# The actual Hom path factorization for original fixed-object strict groupoids

Reuse the native simplicial interval endpoint-pair fibration and path homotopy.
The constant and paired endpoint maps are literally those already constructed
on the original fixed-object groupoids. Their full diagonal factorization is a
weak-equivalence/fibration factorization on every original Hom. This does not
by itself construct the full fixed-object groupoid model structure.
-/

set_option autoImplicit false
open CategoryTheory MonoidalCategory MonoidalClosed HomotopicalAlgebra Simplicial DaggerModels
open DaggerOriginalFixedObjectSimplicialCategories DaggerOriginalFixedObjectDaggerCategories
open DaggerOriginalFixedObjectCotensors DaggerOriginalFixedObjectStrictGroupoidCotensors
open DaggerOriginalFixedObjectCotensorPoints DaggerOriginalFixedObjectGroupoidInterval
open scoped SSet.modelCategoryQuillen
universe u

namespace DaggerOriginalFixedObjectGroupoidHomPathFactorization

noncomputable section

/-- The original paired endpoint map is exactly the existing native simplicial path map. -/
theorem endpointPair_eq_native (X : SSet.{u}) : endpointPair X = X.pathEv₀₁ := rfl

/-- The original constant Hom map is exactly the native constant-path map. -/
theorem constantHom_eq_native (X : SSet.{u}) : constantHom Δ[1] X = X.pathConst := rfl

/-- Native path contraction proves an inverse up to homotopy for the original constant map. -/
def constantHom_homotopyEquiv (X : SSet.{u}) : SSet.HomotopyEquiv X X.path where
  hom := constantHom Δ[1] X
  inv := pointEvaluation (intervalPoint 0) X
  homInvId := .ofEq (congrArg SSet.Subcomplex.RelativeMorphism.botEquiv.symm
    (constantHom_evaluation (intervalPoint 0) X))
  invHomId := X.pathHomotopy

/-- The original constant map is a weak equivalence for every Kan original Hom object. -/
theorem constantHom_weakEquivalence (X : SSet.{u}) [X.KanComplex] :
    WeakEquivalence (constantHom Δ[1] X) :=
  (SSet.weakEquivalence_iff_kanComplexW _).2
    (SSet.KanComplex.W.homotopyEquivHom (constantHom_homotopyEquiv X))

/-- The actual paired endpoint map is a fibration, by the native boundary-one comparison. -/
theorem endpointPair_fibration (X : SSet.{u}) [X.KanComplex] :
    Fibration (endpointPair X) := by
  change Fibration X.pathEv₀₁
  infer_instance

/-- Every original strict groupoid constant functor is a weak equivalence on each Hom. -/
theorem strictConstant_hom_weakEquivalence {O : Type u} (C : FixedStrictGroupoids O)
    (x y : O) : WeakEquivalence ((strictConstant Δ[1] C).hom.map x y) := by
  have : (C.obj.enriched.Hom x y).KanComplex := fixedStrictHom_kan C x y
  exact constantHom_weakEquivalence (C.obj.enriched.Hom x y)

/-- Every original strict dagger constant functor is a weak equivalence on each original Hom. -/
theorem strictDaggerConstant_hom_weakEquivalence {O : Type u}
    (C : FixedStrictDaggerGroupoids O) (x y : O) :
    WeakEquivalence ((strictDaggerConstant Δ[1] C).hom.underlying.map x y) := by
  have : (C.obj.underlying.enriched.Hom x y).KanComplex :=
    fixedStrictHom_kan ⟨C.obj.underlying, C.property⟩ x y
  exact constantHom_weakEquivalence (C.obj.underlying.enriched.Hom x y)

/-- The diagonal on every unchanged original Hom factors with both exact native model classes. -/
theorem strictHom_pathFactorization {O : Type u} (C : FixedStrictGroupoids O) (x y : O) :
    WeakEquivalence ((strictConstant Δ[1] C).hom.map x y) ∧
      Fibration (endpointPair (C.obj.enriched.Hom x y)) ∧
      (strictConstant Δ[1] C).hom.map x y ≫ endpointPair (C.obj.enriched.Hom x y) =
        CartesianMonoidalCategory.lift (𝟙 (C.obj.enriched.Hom x y))
          (𝟙 (C.obj.enriched.Hom x y)) := by
  have : (C.obj.enriched.Hom x y).KanComplex := fixedStrictHom_kan C x y
  exact ⟨strictConstant_hom_weakEquivalence C x y, endpointPair_fibration _,
    constant_endpointPair _⟩

/-- The same entire Hom factorization holds for the original strict dagger interval diagram. -/
theorem strictDaggerHom_pathFactorization {O : Type u} (C : FixedStrictDaggerGroupoids O)
    (x y : O) :
    WeakEquivalence ((strictDaggerConstant Δ[1] C).hom.underlying.map x y) ∧
      Fibration (endpointPair (C.obj.underlying.enriched.Hom x y)) ∧
      (strictDaggerConstant Δ[1] C).hom.underlying.map x y ≫
          endpointPair (C.obj.underlying.enriched.Hom x y) =
        CartesianMonoidalCategory.lift (𝟙 (C.obj.underlying.enriched.Hom x y))
          (𝟙 (C.obj.underlying.enriched.Hom x y)) := by
  have : (C.obj.underlying.enriched.Hom x y).KanComplex :=
    fixedStrictHom_kan ⟨C.obj.underlying, C.property⟩ x y
  exact ⟨strictDaggerConstant_hom_weakEquivalence C x y, endpointPair_fibration _,
    constant_endpointPair _⟩

end

end DaggerOriginalFixedObjectGroupoidHomPathFactorization
