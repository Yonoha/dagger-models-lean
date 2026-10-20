import OriginalFullVertexWeakEquivalenceRestriction
import OriginalEC2CanonicalVertexKan

/-!
# Weak equivalences of the original canonical-vertex restriction

The existing canonical vertex map is identified with the universal full
subcomplex restriction of the very same original equivariant singular map.
An ambient weak equivalence therefore restricts to a weak equivalence exactly
when the original canonical restriction covers its connected components.
This is a conditional restriction theorem, not full dagger Joyal recognition.
-/

set_option autoImplicit false

open CategoryTheory DaggerModels Opposite Simplicial HomotopicalAlgebra
open DaggerOriginalEC2HomotopyFixedPointObject DaggerOriginalEC2HomotopyFixedPointFunctor
open DaggerOriginalDaggerRealizationContinuousAction DaggerOriginalEC2CanonicalVertexSubcomplex
open DaggerOriginalEC2CanonicalVertexKan DaggerOriginalFullVertexWeakEquivalenceRestriction
open scoped SSet.modelCategoryQuillen

universe u

namespace DaggerOriginalCanonicalVertexWeakEquivalenceRestriction

noncomputable section

/-- The original ambient map carries the original selected vertices to selected vertices. -/
theorem canonicalVertices_map {K L : DaggerSSet.{u}} (f : K ⟶ L) :
    ∀ x, x ∈ canonicalVertices K →
      (daggerHomotopyFixedPointFunctor.map f).app (op ⦋0⦌) x ∈ canonicalVertices L := by
  rintro _ ⟨x, rfl⟩
  exact ⟨f.hom.app (op ⦋0⦌) x, (canonicalZeroSimplex_naturality f x).symm⟩

/-- The pre-existing canonical map is the restriction of the same ambient arrow. -/
theorem canonicalVertexMap_eq_restrictedMap {K L : DaggerSSet.{u}} (f : K ⟶ L) :
    canonicalVertexMap f = restrictedMap (canonicalVertices K) (canonicalVertices L)
      (daggerHomotopyFixedPointFunctor.map f) (canonicalVertices_map f) := by
  apply NatTrans.ext
  funext n s
  apply Subtype.ext
  rfl

/-- An actual ambient weak equivalence restricts to the original canonical vertex map. -/
theorem canonicalVertexMap_weakEquivalence {K L : DaggerSSet.{u}} (f : K ⟶ L)
    [WeakEquivalence (daggerHomotopyFixedPointFunctor.map f)]
    (hπ₀ : Function.Surjective (SSet.mapπ₀ (canonicalVertexMap f))) :
    WeakEquivalence (canonicalVertexMap f) := by
  have : SSet.KanComplex (daggerHomotopyFixedPointFunctor.obj K) :=
    mappingSing_kan (realizedContinuousActionFunctor.obj K)
  have : SSet.KanComplex (daggerHomotopyFixedPointFunctor.obj L) :=
    mappingSing_kan (realizedContinuousActionFunctor.obj L)
  rw [canonicalVertexMap_eq_restrictedMap] at hπ₀ ⊢
  exact restrictedMap_weakEquivalence _ _ _ _ hπ₀

/-- A weak equivalence of the actual canonical restriction covers its actual components. -/
theorem canonicalVertexMap_mapπ₀_surjective {K L : DaggerSSet.{u}} (f : K ⟶ L)
    [WeakEquivalence (canonicalVertexMap f)] :
    Function.Surjective (SSet.mapπ₀ (canonicalVertexMap f)) :=
  ((SSet.KanComplex.isEquivalence_mapFundamentalGroupoid_iff _).1
    ((SSet.weakEquivalence_iff_kanComplexW _).1 inferInstance).isEquivalence).1.2

/-- Under the ambient weak equivalence, the exact canonical restriction is recognized by π₀. -/
theorem canonicalVertexMap_weakEquivalence_iff {K L : DaggerSSet.{u}} (f : K ⟶ L)
    [WeakEquivalence (daggerHomotopyFixedPointFunctor.map f)] :
    WeakEquivalence (canonicalVertexMap f) ↔
      Function.Surjective (SSet.mapπ₀ (canonicalVertexMap f)) := by
  constructor
  · intro hf
    exact canonicalVertexMap_mapπ₀_surjective f
  · exact canonicalVertexMap_weakEquivalence f

end

end DaggerOriginalCanonicalVertexWeakEquivalenceRestriction
