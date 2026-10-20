import OriginalSimplicialCotensorRestriction
import OriginalFixedObjectGroupoidInterval

/-!
# Original fixed-object groupoid cotensor fibrations

All original strict groupoid Hom objects are already Kan. Apply the native
cotensor restriction theorem to those exact Hom objects. Every global-point
evaluation is a native simplicial fibration, via the proved unit-evaluation
isomorphism. No fixed-object model structure or path-object recognition is
assumed in these proofs.
-/

set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory MonoidalClosed HomotopicalAlgebra DaggerModels
open DaggerOriginalFixedObjectSimplicialCategories DaggerOriginalFixedObjectDaggerCategories
open DaggerOriginalFixedObjectCotensors DaggerOriginalFixedObjectStrictGroupoidCotensors
open DaggerOriginalFixedObjectCotensorPoints DaggerOriginalSimplicialCotensorRestriction
open DaggerOriginalFixedObjectGroupoidInterval
open scoped SSet.modelCategoryQuillen
universe u

namespace DaggerOriginalFixedObjectCotensorFibrations

noncomputable section

/-- Evaluation at any actual global point of a Kan cotensor is a native fibration. -/
theorem pointEvaluation_fibration {K : SSet.{u}} (a : 𝟙_ SSet.{u} ⟶ K)
    (X : SSet.{u}) [X.KanComplex] : Fibration (pointEvaluation a X) := by
  have : Fibration ((MonoidalClosed.pre a).app X) := pre_fibration a X
  have h := pointEvaluation_parameter a (𝟙 (𝟙_ SSet.{u})) X
  simp only [Category.id_comp] at h
  rw [← h]
  infer_instance

/-- Every exact original Hom restriction along a monomorphism is a native fibration. -/
theorem strictPre_hom_fibration {K L : SSet.{u}} (i : K ⟶ L) [Mono i]
    {O : Type u} (C : FixedStrictGroupoids O) (x y : O) :
    Fibration ((cotensorPre i C.obj).map x y) := by
  have : (C.obj.enriched.Hom x y).KanComplex := fixedStrictHom_kan C x y
  exact pre_fibration i (C.obj.enriched.Hom x y)

/-- Every exact original Hom restriction along an anodyne parameter is a trivial fibration. -/
theorem strictPre_hom_trivialFibration {K L : SSet.{u}} (i : K ⟶ L)
    (hi : SSet.anodyneExtensions i) {O : Type u} (C : FixedStrictGroupoids O) (x y : O) :
    trivialFibrations SSet.{u} ((cotensorPre i C.obj).map x y) := by
  have : (C.obj.enriched.Hom x y).KanComplex := fixedStrictHom_kan C x y
  exact pre_trivialFibration i hi (C.obj.enriched.Hom x y)

/-- Each original fixed-object strict groupoid point evaluation is a fibration on every Hom. -/
theorem strictEvaluation_hom_fibration {K : SSet.{u}} (a : 𝟙_ SSet.{u} ⟶ K)
    {O : Type u} (C : FixedStrictGroupoids O) (x y : O) :
    Fibration ((strictEvaluation a C).hom.map x y) := by
  have : (C.obj.enriched.Hom x y).KanComplex := fixedStrictHom_kan C x y
  exact pointEvaluation_fibration a (C.obj.enriched.Hom x y)

/-- The original dagger evaluations have the same native Hom fibrations. -/
theorem strictDaggerEvaluation_hom_fibration {K : SSet.{u}} (a : 𝟙_ SSet.{u} ⟶ K)
    {O : Type u} (C : FixedStrictDaggerGroupoids O) (x y : O) :
    Fibration ((strictDaggerEvaluation a C).hom.underlying.map x y) := by
  have : (C.obj.underlying.enriched.Hom x y).KanComplex :=
    fixedStrictHom_kan ⟨C.obj.underlying, C.property⟩ x y
  exact pointEvaluation_fibration a (C.obj.underlying.enriched.Hom x y)

/-- Both actual ordinary interval endpoints are native fibrations on every original Hom. -/
theorem intervalEndpoint_hom_fibration {O : Type u} (C : FixedStrictGroupoids O)
    (v : Fin 2) (x y : O) : Fibration (((evaluationNat O v).app C).hom.map x y) :=
  strictEvaluation_hom_fibration (intervalPoint v) C x y

/-- Both actual dagger interval endpoints are native fibrations on every original Hom. -/
theorem daggerIntervalEndpoint_hom_fibration {O : Type u} (C : FixedStrictDaggerGroupoids O)
    (v : Fin 2) (x y : O) :
    Fibration (((daggerEvaluationNat O v).app C).hom.underlying.map x y) :=
  strictDaggerEvaluation_hom_fibration (intervalPoint v) C x y

end

end DaggerOriginalFixedObjectCotensorFibrations
