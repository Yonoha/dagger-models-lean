import OriginalEC2HomotopyFixedPointFunctor
import OriginalFullVertexSubcomplex

/-!
# The actual canonical-vertex full subcomplex

This is the point-set full subcomplex of the original singular equivariant
mapping object spanned by the original canonical constant vertices. It does
not replace the missing maximal Kan core of a dagger quasi-category.
-/

set_option autoImplicit false

open CategoryTheory DaggerModels Opposite Simplicial
open DaggerOriginalDaggerRealizationContinuousAction
open DaggerOriginalEquivariantConstantMaps
open DaggerOriginalEC2RealizationAction
open DaggerOriginalEC2HomotopyFixedPointObject
open DaggerOriginalEC2HomotopyFixedPointFunctor
open DaggerOriginalFullVertexSubcomplex

universe u

namespace DaggerOriginalEC2CanonicalVertexSubcomplex

noncomputable section

/-- Exactly the constant vertices associated to the original dagger vertices. -/
def canonicalVertices (K : DaggerSSet.{u}) :
    Set ((daggerHomotopyFixedPointFunctor.obj K).obj (op ⦋0⦌)) :=
  Set.range (canonicalZeroSimplex K)

/-- The full subcomplex spanned by the actual canonical constant vertices. -/
def canonicalVertexSubcomplex (K : DaggerSSet.{u}) :
    (daggerHomotopyFixedPointFunctor.obj K).Subcomplex :=
  fullVertexSubcomplex _ (canonicalVertices K)

/-- Canonical vertices are natural for the actual realized dagger morphisms. -/
theorem canonicalZeroSimplex_naturality {K L : DaggerSSet.{u}} (f : K ⟶ L)
    (x : K.toSSet _⦋0⦌) :
    (daggerHomotopyFixedPointFunctor.map f).app (op ⦋0⦌)
      (canonicalZeroSimplex K x) = canonicalZeroSimplex L (f.hom.app (op ⦋0⦌) x) := by
  apply (TopCat.toSSetObjEquiv
    (mappingTop (realizedContinuousActionFunctor.obj L)) (op ⦋0⦌)).injective
  ext t
  apply Subtype.ext
  exact canonicalConstantMap_naturality realizedEC2ContinuousAction f x

/-- Every vertex of a selected simplex is an actual canonical constant map. -/
theorem mem_canonicalVertexSubcomplex_iff (K : DaggerSSet.{u})
    (n : SimplexCategoryᵒᵖ) (s : (daggerHomotopyFixedPointFunctor.obj K).obj n) :
    s ∈ (canonicalVertexSubcomplex K).obj n ↔
      ∀ v : ⦋0⦌ ⟶ n.unop, ∃ x : K.toSSet _⦋0⦌,
        canonicalZeroSimplex K x = (daggerHomotopyFixedPointFunctor.obj K).map v.op s :=
  Iff.rfl

/-- The actual singular mapping morphism restricts to the canonical full subcomplex. -/
def canonicalVertexMap {K L : DaggerSSet.{u}} (f : K ⟶ L) :
    (canonicalVertexSubcomplex K).toSSet ⟶ (canonicalVertexSubcomplex L).toSSet where
  app n s := ⟨(daggerHomotopyFixedPointFunctor.map f).app n s.1, by
    intro v
    obtain ⟨x, hx⟩ := s.2 v
    refine ⟨f.hom.app (op ⦋0⦌) x, ?_⟩
    rw [← canonicalZeroSimplex_naturality f x, hx]
    exact congrFun ((daggerHomotopyFixedPointFunctor.map f).naturality v.op) s.1⟩
  naturality m n g := by
    ext s
    apply Subtype.ext
    exact congrFun ((daggerHomotopyFixedPointFunctor.map f).naturality g) s.1

end

end DaggerOriginalEC2CanonicalVertexSubcomplex
