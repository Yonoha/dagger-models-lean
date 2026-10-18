import NativeRealEdgewiseCanonicalPart
import NativeKanRigHomWeakRecognition

/-! Weakness of the literal canonical-vertex restriction, with explicit coverage of vertices. -/
set_option autoImplicit false
open CategoryTheory Opposite Simplicial HomotopicalAlgebra DaggerModels
open DaggerNativeRealEdgewiseCanonicalConstants DaggerNativeRealEdgewiseCanonicalPart
open DaggerNativeRealEdgewiseContinuousComparison
open DaggerNativeRealEdgewiseHomotopyFixedPointComparison
open DaggerOriginalEC2HomotopyFixedPointObject DaggerOriginalEC2HomotopyFixedPointFunctor
open DaggerOriginalEC2CanonicalVertexSubcomplex DaggerOriginalDaggerRealizationContinuousAction
open DaggerOriginalFullVertexSubcomplex DaggerOriginalFullVertexWeakEquivalenceRestriction
open DaggerOriginalFullVertexPointedHomotopyComparison
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerNativeRealEdgewiseCanonicalWeak
noncomputable section

def canonicalVertex (X : DaggerSSet.{u}) (x : X.toSSet _⦋0⦌) :
    (canonicalFunctor.obj X).obj (op ⦋0⦌) :=
  ⟨edgewiseCanonicalZero X x, by
    intro v
    have hv : v = 𝟙 ⦋0⦌ := Subsingleton.elim _ _
    subst v
    simpa using (show edgewiseCanonicalZero X x ∈ vertices X from ⟨x, rfl⟩)⟩

theorem comparison_canonicalVertex (X : DaggerSSet.{u}) (x : X.toSSet _⦋0⦌) :
    ((comparison X).app (op ⦋0⦌) (canonicalVertex X x)).val = canonicalZeroSimplex X x :=
  canonicalZero_comparison X x

theorem comparison_zero_surjective (X : DaggerSSet.{u}) :
    Function.Surjective ((comparison X).app (op ⦋0⦌)) := by
  intro a
  have ha : a.val ∈ canonicalVertices X := fullVertex_vertex_mem _ a
  obtain ⟨x, hx⟩ := ha
  refine ⟨canonicalVertex X x, ?_⟩
  apply Subtype.ext
  exact (comparison_canonicalVertex X x).trans hx

theorem comparison_piZero_surjective (X : DaggerSSet.{u}) :
    Function.Surjective (SSet.mapπ₀ (comparison X)) :=
  DaggerNativeKanRigHomWeakRecognition.mapπ₀_surjective_of_vertices
    (comparison X) (comparison_zero_surjective X)

theorem comparison_weak (X : DaggerSSet.{u}) : WeakEquivalence (comparison X) := by
  have : SSet.KanComplex (edgewiseHomotopyFixedPointFunctor.obj X) :=
    mappingSing_kan (realizedEdgewiseContinuousFunctor.obj X)
  have : SSet.KanComplex (daggerHomotopyFixedPointFunctor.obj X) :=
    mappingSing_kan (realizedContinuousActionFunctor.obj X)
  have : WeakEquivalence (homotopyFixedPointComparison.app X) :=
    homotopyFixedPointComparison_weak X
  exact restrictedMap_weakEquivalence (vertices X) (canonicalVertices X)
    (homotopyFixedPointComparison.app X) (comparison_preservesVertices X)
      (comparison_piZero_surjective X)

theorem comparison_kanWeak (X : DaggerSSet.{u}) : SSet.KanComplex.W (comparison X) := by
  have : SSet.KanComplex (canonicalFunctor.obj X) := canonicalSubcomplex_kan X
  have : SSet.KanComplex (DaggerOriginalEC2CanonicalVertexKan.canonicalVertexFunctor.obj X) :=
    DaggerOriginalEC2CanonicalVertexKan.canonicalVertexSubcomplex_kan X
  exact (SSet.weakEquivalence_iff_kanComplexW _).mp (comparison_weak X)

end
end DaggerNativeRealEdgewiseCanonicalWeak
