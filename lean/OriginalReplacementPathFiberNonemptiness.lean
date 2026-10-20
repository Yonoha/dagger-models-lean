import OriginalStrictPathFiberVertices
import OriginalStrictPathFiberReplacement

/-!
# Nonemptiness of the actual specified replacement path fiber

For a Kan target and any specified weak point replacement whose second
leg is a fibration, the literal replacement pullback is fibrant. Native
right properness and actual component surjectivity transport existence of
vertices along the original strict comparison map. Thus its nonemptiness
is equivalent to equality of the same original endpoint components.
-/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite Simplicial HomotopicalAlgebra
open MonoidalCategory
open DaggerOriginalFullVertexSubcomplex DaggerOriginalStrictPathFiberReplacement
open DaggerOriginalStrictPathFiberVertices
open scoped SSet.modelCategoryQuillen

universe u

namespace DaggerOriginalReplacementPathFiberNonemptiness

noncomputable section

/-- The specified replacement pullback itself is fibrant, with its original endpoint map. -/
theorem replacementPathFiber_fibrant {X R : SSet.{u}} [X.KanComplex]
    (p : R ⟶ X ⊗ X) [Fibration p] : IsFibrant (pullback X.pathEv₀₁ p) := by
  have : IsFibrant X.path := inferInstance
  have : Fibration (pullback.fst X.pathEv₀₁ p) := inferInstance
  rw [isFibrant_iff, Subsingleton.elim (terminal.from (pullback X.pathEv₀₁ p))
    (pullback.fst X.pathEv₀₁ p ≫ terminal.from X.path)]
  infer_instance

/-- The exact comparison retains nonemptiness in both directions. -/
theorem comparison_vertices_nonempty_iff {X R : SSet.{u}} [X.KanComplex]
    (a b : X.obj (op ⦋0⦌)) (i : (Δ[0] : SSet.{u}) ⟶ R) (p : R ⟶ X ⊗ X)
    (hpoint : i ≫ p = SSet.yonedaEquiv.symm (a, b)) [WeakEquivalence i] [Fibration p] :
    Nonempty ((strictPathFiber X a b : SSet).obj (op ⦋0⦌)) ↔
      Nonempty ((pullback X.pathEv₀₁ p).obj (op ⦋0⦌)) := by
  haveI := strictPathEndpoint_fibration X
  haveI := strictPathFiber_fibrant X a b
  haveI := replacementPathFiber_fibrant p
  haveI := comparison_weakEquivalence X.pathEv₀₁ (a, b) i p hpoint
  exact vertices_nonempty_iff_of_weakEquivalence (comparison X.pathEv₀₁ (a, b) i p hpoint)

/-- The actual replacement fiber has a vertex exactly when the original endpoints agree in π₀.
-/
theorem replacementPathFiber_vertex_nonempty_iff {X R : SSet.{u}} [X.KanComplex]
    (a b : X.obj (op ⦋0⦌)) (i : (Δ[0] : SSet.{u}) ⟶ R) (p : R ⟶ X ⊗ X)
    (hpoint : i ≫ p = SSet.yonedaEquiv.symm (a, b)) [WeakEquivalence i] [Fibration p] :
    Nonempty ((pullback X.pathEv₀₁ p).obj (op ⦋0⦌)) ↔ SSet.π₀.mk a = SSet.π₀.mk b :=
  (comparison_vertices_nonempty_iff a b i p hpoint).symm.trans
    (strictPathFiber_vertex_nonempty_iff X a b)

end

end DaggerOriginalReplacementPathFiberNonemptiness
