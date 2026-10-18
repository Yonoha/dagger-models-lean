import NativeOriginalStrictHomUnitaryExistence
import ActualOriginalUnitaryCoreCompletionComparison

/-! Apply the strict Hom theorem to the FULL completed core
of EVERY original dagger quasi-category. -/
set_option autoImplicit false
open CategoryTheory Opposite Simplicial HomotopicalAlgebra DaggerModels OrdinaryRigidification
open DaggerActualDaggerOrdinaryCore DaggerOriginalUnitaryCoreConstruction
open DaggerOriginalUnitaryCoreCanonicalVertices DaggerNativeOriginalRealSigmaAnchors
open DaggerOriginalSimplicialGroupoidCompletionUniversal DaggerNativeKanWeakComponents
open DaggerOriginalStrictDaggerGroupoidDerivedMapping
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerNativeOriginalCompletedCoreUnitaryExistence
noncomputable section

variable (X : DaggerSSet.{u}) [X.toSSet.Quasicategory]

def fullCompletion : DaggerSimplicialCat.{u, u} :=
  DaggerActualCanonicalDaggerKanCompletionUnit.target (coreDagger X)

def fullCompletion_strict : IsStrictGroupoid (fullCompletion X).toSimplicialCat :=
  completion_isStrictGroupoid (DaggerRigidification.obj (coreDagger X)).toSimplicialCat

def coreVertex (x : X.toSSet _⦋0⦌) : (coreDagger X).toSSet _⦋0⦌ :=
  (coreVerticesEquiv X).symm x

theorem coreVertex_value (x : X.toSSet _⦋0⦌) :
    (DaggerActualDaggerOrdinaryCoreMaps.inclusion X).hom.app (op ⦋0⦌) (coreVertex X x) = x :=
  (coreVerticesEquiv X).apply_symm_apply x

def completedVertex (x : X.toSSet _⦋0⦌) : Labels (fullCompletion X) :=
  (DaggerActualCanonicalDaggerKanCompletionUnit.unit (coreDagger X)).hom.app (op ⦋0⦌)
    (coreVertex X x)

theorem completedVertex_label (x : X.toSSet _⦋0⦌) :
    label (fullCompletion X) (completedVertex X x) =
      DaggerActualRigidifiedDaggerCoreCompletion.endpoint X x :=
  DaggerActualCanonicalDaggerKanCompletionUnit.vertex (coreDagger X) (coreVertex X x)

theorem original_completed_components_iff (x y : X.toSSet _⦋0⦌) :
    SSet.π₀.mk (canonicalUnitaryVertex X x) = SSet.π₀.mk (canonicalUnitaryVertex X y) ↔
      SSet.π₀.mk (canonicalUnitaryVertex
          (DaggerNerve.daggerCoherentNerve.obj (fullCompletion X)) (completedVertex X x)) =
        SSet.π₀.mk (canonicalUnitaryVertex
          (DaggerNerve.daggerCoherentNerve.obj (fullCompletion X)) (completedVertex X y)) := by
  have : (unitaryCore X).KanComplex := unitaryCore_kan X
  have : (unitaryCore (coreDagger X)).KanComplex := unitaryCore_kan _
  have :
      (unitaryCore
        (DaggerActualOriginalUnitaryCoreCompletionComparison.completedNerve X)).KanComplex :=
    unitaryCore_kan _
  let eL := equivalence (DaggerActualOriginalUnitaryCoreCompletionComparison.left X)
    (DaggerActualOriginalUnitaryCoreCompletionComparison.left_weak X)
  let eR := equivalence (DaggerActualOriginalUnitaryCoreCompletionComparison.right X)
    (DaggerActualOriginalUnitaryCoreCompletionComparison.right_weak X)
  have hLx : eL (SSet.π₀.mk (canonicalUnitaryVertex (coreDagger X) (coreVertex X x))) =
      SSet.π₀.mk (canonicalUnitaryVertex X x) :=
    equivalence_vertex _ _ _ _
      ((DaggerActualOriginalUnitaryCoreCompletionComparison.left_vertex X (coreVertex X x)).trans
        (congrArg (canonicalUnitaryVertex X) (coreVertex_value X x)))
  have hLy : eL (SSet.π₀.mk (canonicalUnitaryVertex (coreDagger X) (coreVertex X y))) =
      SSet.π₀.mk (canonicalUnitaryVertex X y) :=
    equivalence_vertex _ _ _ _
      ((DaggerActualOriginalUnitaryCoreCompletionComparison.left_vertex X (coreVertex X y)).trans
        (congrArg (canonicalUnitaryVertex X) (coreVertex_value X y)))
  have hRx : eR (SSet.π₀.mk (canonicalUnitaryVertex (coreDagger X) (coreVertex X x))) =
      SSet.π₀.mk (canonicalUnitaryVertex
        (DaggerNerve.daggerCoherentNerve.obj (fullCompletion X)) (completedVertex X x)) :=
    equivalence_vertex _ _ _ _
      (DaggerActualOriginalUnitaryCoreCompletionComparison.right_vertex X (coreVertex X x))
  have hRy : eR (SSet.π₀.mk (canonicalUnitaryVertex (coreDagger X) (coreVertex X y))) =
      SSet.π₀.mk (canonicalUnitaryVertex
        (DaggerNerve.daggerCoherentNerve.obj (fullCompletion X)) (completedVertex X y)) :=
    equivalence_vertex _ _ _ _
      (DaggerActualOriginalUnitaryCoreCompletionComparison.right_vertex X (coreVertex X y))
  rw [← hLx, ← hLy, ← hRx, ← hRy]
  exact ⟨fun h ↦ congrArg eR (eL.injective h), fun h ↦ congrArg eL (eR.injective h)⟩

theorem derived_completed_vertices_iff_original_unitary (x y : X.toSSet _⦋0⦌) :
    Nonempty ((strictDerivedMapping (fullCompletion X) (fullCompletion_strict X)
      (DaggerActualRigidifiedDaggerCoreCompletion.endpoint X x)
      (DaggerActualRigidifiedDaggerCoreCompletion.endpoint X y)) _⦋0⦌) ↔
        SSet.π₀.mk (canonicalUnitaryVertex X x) = SSet.π₀.mk (canonicalUnitaryVertex X y) := by
  have h := DaggerNativeOriginalStrictHomUnitaryExistence.derived_vertices_iff_original_unitary
    (fullCompletion X) (fullCompletion_strict X) (completedVertex X x) (completedVertex X y)
  rw [completedVertex_label, completedVertex_label] at h
  exact h.trans (original_completed_components_iff X x y).symm

end
end DaggerNativeOriginalCompletedCoreUnitaryExistence
