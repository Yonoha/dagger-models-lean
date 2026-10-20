import OriginalFibrantPathLifting
import OriginalSimplicialPathHomotopy

/-!
# Actual lifting acyclicity for original fixed-object strict groupoids

For the precise original Homwise fibration class, its entire left lifting
class consists of original Homwise weak equivalences. Ordinary and dagger
versions use the native good path objects and actual fibrancy proved earlier.
The model structure is not assumed to establish this transfer condition.
-/

set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory HomotopicalAlgebra Simplicial DaggerModels
open DaggerOriginalFixedObjectSimplicialCategories DaggerOriginalFixedObjectDaggerCategories
open DaggerOriginalFixedObjectGroupoidClasses DaggerOriginalFixedObjectGroupoidPathObjects
open DaggerOriginalFixedObjectGroupoidTerminals DaggerOriginalFibrantPathLifting
open DaggerOriginalSimplicialPathHomotopy DaggerOriginalFixedObjectCotensorPoints
open DaggerOriginalFixedObjectGroupoidInterval
open scoped SSet.modelCategoryQuillen DaggerOriginalFixedObjectGroupoidClasses
universe u

namespace DaggerOriginalFixedObjectGroupoidAcyclicity

noncomputable section

/-- Lifting against all original fibrations produces an entire retraction and interval path. -/
def strictRetractionPath {O : Type u} {C D : FixedStrictGroupoids O} (i : C ⟶ D)
    (hi : (strictFibrations O).llp i) :
    RetractionPathData i (strictPath D).toPrepathObject := by
  have : HasLiftingProperty i (terminal.from C) :=
    hi _ ((fibration_iff (terminal.from C)).1 inferInstance)
  have : HasLiftingProperty i (strictPath D).p :=
    hi _ ((fibration_iff (strictPath D).p).1 inferInstance)
  exact liftingRetractionPath i (strictPath D).toPrepathObject

/-- The actual full retraction and path give a native homotopy inverse on every original Hom. -/
def strictHomotopyEquiv {O : Type u} {C D : FixedStrictGroupoids O} (i : C ⟶ D)
    (hi : (strictFibrations O).llp i) (x y : O) :
    SSet.HomotopyEquiv (C.obj.enriched.Hom x y) (D.obj.enriched.Hom x y) := by
  let d := strictRetractionPath i hi
  have hir := congrArg (fun f : C ⟶ C ↦ f.hom.map x y) d.i_r
  change i.hom.map x y ≫ d.r.hom.map x y = 𝟙 _ at hir
  have h₀ := congrArg (fun f : D ⟶ D ↦ f.hom.map x y) d.H_p₀
  have h₁ := congrArg (fun f : D ⟶ D ↦ f.hom.map x y) d.H_p₁
  change d.H.hom.map x y ≫ pointEvaluation (intervalPoint 0) _ =
    d.r.hom.map x y ≫ i.hom.map x y at h₀
  change d.H.hom.map x y ≫ pointEvaluation (intervalPoint 1) _ = 𝟙 _ at h₁
  refine ⟨i.hom.map x y, d.r.hom.map x y,
    .ofEq (congrArg SSet.Subcomplex.RelativeMorphism.botEquiv.symm hir), ?_⟩
  rw [← h₀, ← h₁]
  exact endpointHomotopy (d.H.hom.map x y)

/-- Every arrow in the actual fibration left lifting class is an original weak equivalence. -/
theorem strict_llp_weakEquivalence {O : Type u} {C D : FixedStrictGroupoids O}
    (i : C ⟶ D) (hi : (strictFibrations O).llp i) : WeakEquivalence i := by
  apply (strict_weakEquivalence_iff _).2
  intro x y
  have : (C.obj.enriched.Hom x y).KanComplex := fixedStrictHom_kan C x y
  have : (D.obj.enriched.Hom x y).KanComplex := fixedStrictHom_kan D x y
  exact (SSet.weakEquivalence_iff_kanComplexW _).2
    (SSet.KanComplex.W.homotopyEquivHom (strictHomotopyEquiv i hi x y))

/-- The entire original ordinary transfer acyclicity condition, with no additional premise. -/
theorem strictFibrations_llp_le_weakEquivalences (O : Type u) :
    (strictFibrations O).llp ≤ strictWeakEquivalences O := by
  intro C D i hi
  exact (weakEquivalence_iff i).1 (strict_llp_weakEquivalence i hi)

/-- The same lifting construction retains the entire original dagger functor. -/
def strictDaggerRetractionPath {O : Type u} {C D : FixedStrictDaggerGroupoids O}
    (i : C ⟶ D) (hi : (strictDaggerFibrations O).llp i) :
    RetractionPathData i (strictDaggerPath D).toPrepathObject := by
  have : HasLiftingProperty i (terminal.from C) :=
    hi _ ((fibration_iff (terminal.from C)).1 inferInstance)
  have : HasLiftingProperty i (strictDaggerPath D).p :=
    hi _ ((fibration_iff (strictDaggerPath D).p).1 inferInstance)
  exact liftingRetractionPath i (strictDaggerPath D).toPrepathObject

/-- Every unchanged original dagger Hom has the native homotopy inverse of its original map. -/
def strictDaggerHomotopyEquiv {O : Type u} {C D : FixedStrictDaggerGroupoids O}
    (i : C ⟶ D) (hi : (strictDaggerFibrations O).llp i) (x y : O) :
    SSet.HomotopyEquiv (C.obj.underlying.enriched.Hom x y)
      (D.obj.underlying.enriched.Hom x y) := by
  let d := strictDaggerRetractionPath i hi
  have hir := congrArg (fun f : C ⟶ C ↦ f.hom.underlying.map x y) d.i_r
  change i.hom.underlying.map x y ≫ d.r.hom.underlying.map x y = 𝟙 _ at hir
  have h₀ := congrArg (fun f : D ⟶ D ↦ f.hom.underlying.map x y) d.H_p₀
  have h₁ := congrArg (fun f : D ⟶ D ↦ f.hom.underlying.map x y) d.H_p₁
  change d.H.hom.underlying.map x y ≫ pointEvaluation (intervalPoint 0) _ =
    d.r.hom.underlying.map x y ≫ i.hom.underlying.map x y at h₀
  change d.H.hom.underlying.map x y ≫ pointEvaluation (intervalPoint 1) _ = 𝟙 _ at h₁
  refine ⟨i.hom.underlying.map x y, d.r.hom.underlying.map x y,
    .ofEq (congrArg SSet.Subcomplex.RelativeMorphism.botEquiv.symm hir), ?_⟩
  rw [← h₀, ← h₁]
  exact endpointHomotopy (d.H.hom.underlying.map x y)

/-- The dagger fibration left lifting class consists of actual original weak equivalences. -/
theorem strictDagger_llp_weakEquivalence {O : Type u} {C D : FixedStrictDaggerGroupoids O}
    (i : C ⟶ D) (hi : (strictDaggerFibrations O).llp i) : WeakEquivalence i := by
  apply (strictDagger_weakEquivalence_iff _).2
  intro x y
  have : (C.obj.underlying.enriched.Hom x y).KanComplex :=
    fixedStrictHom_kan ⟨C.obj.underlying, C.property⟩ x y
  have : (D.obj.underlying.enriched.Hom x y).KanComplex :=
    fixedStrictHom_kan ⟨D.obj.underlying, D.property⟩ x y
  exact (SSet.weakEquivalence_iff_kanComplexW _).2
    (SSet.KanComplex.W.homotopyEquivHom (strictDaggerHomotopyEquiv i hi x y))

/-- The entire original dagger transfer acyclicity condition without a model premise. -/
theorem strictDaggerFibrations_llp_le_weakEquivalences (O : Type u) :
    (strictDaggerFibrations O).llp ≤ strictDaggerWeakEquivalences O := by
  intro C D i hi
  exact (weakEquivalence_iff i).1 (strictDagger_llp_weakEquivalence i hi)

end

end DaggerOriginalFixedObjectGroupoidAcyclicity
