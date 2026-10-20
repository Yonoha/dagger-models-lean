import EndomorphismCellStageEquations
import InverseTriangleCellFamily

/-!
# All chosen inverse triangles become strict at one common stage

A finite family of triangle data may use different source objects and different
target diagrams. In particular, both sides of a whole inverse witness use the
same stage. Presentability is required for the complete tensor sources.
-/
set_option autoImplicit false
open CategoryTheory Limits Opposite Simplicial MonoidalCategory
open DaggerNativeHoIsoTriangles DaggerSimplexInverseWitnessCategory
open DaggerInverseTriangleCellFamily
universe u
namespace DaggerTriangleWitnessStageEquations

theorem finite_triangle_squares {J : Type u} [SmallCategory J]
    (κ : Cardinal.{u}) [Fact κ.IsRegular] [IsCardinalFiltered J κ]
    {A : Type u} [Finite A] (X : A → SSet.{u}) (D : A → J ⥤ SSet.{u})
    (c : ∀ a, Cocone (D a)) (hc : ∀ a, IsColimit (c a))
    (hX : ∀ a, IsCardinalPresentable (X a ⊗ Δ[1]) κ ∧
      IsCardinalPresentable (X a ⊗ Δ[2]) κ)
    (x₀ x₁ : ∀ a, SSet.hoFunctor.obj ((ihom (X a)).obj (X a)))
    (d : ∀ a, IsoTriangles ((ihom (X a)).obj (X a)) (x₀ a) (x₁ a))
    (s₀ s₁ : ∀ a j, SSet.hoFunctor.obj ((ihom ((D a).obj j)).obj ((D a).obj j)))
    (s : ∀ a j, IsoTriangles ((ihom ((D a).obj j)).obj ((D a).obj j)) (s₀ a j) (s₁ a j))
    (z₀ z₁ : ∀ a, SSet.hoFunctor.obj ((ihom (c a).pt).obj (c a).pt))
    (z : ∀ a, IsoTriangles ((ihom (c a).pt).obj (c a).pt) (z₀ a) (z₁ a))
    (hleg : ∀ a j, TriangleSquare ((c a).ι.app j) (s a j) (z a))
    (hstage : ∀ a {i j} (f : i ⟶ j), TriangleSquare ((D a).map f) (s a i) (s a j))
    {i : J} (f : ∀ a, X a ⟶ (D a).obj i)
    (hf : ∀ a, TriangleSquare (f a ≫ (c a).ι.app i) (d a) (z a)) :
    ∃ (j : J) (t : i ⟶ j), ∀ a, TriangleSquare (f a ≫ (D a).map t) (d a) (s a j) := by
  let XX : A × Kind → SSet.{u} := fun a ↦ X a.1
  let nn : A × Kind → ℕ := fun a ↦ a.2.degree
  let DD : A × Kind → J ⥤ SSet.{u} := fun a ↦ D a.1
  let cc : ∀ a, Cocone (DD a) := fun a ↦ c a.1
  have hXX : ∀ a, IsCardinalPresentable (XX a ⊗ Δ[nn a]) κ := by
    rintro ⟨a, k⟩
    cases k
    · exact (hX a).1
    · exact (hX a).1
    · exact (hX a).2
    · exact (hX a).2
  obtain ⟨j, t, ht⟩ := DaggerEndomorphismCellStageEquations.finite_cell_squares κ XX nn DD cc
    (fun a ↦ hc a.1) hXX (fun a ↦ cell (d a.1) a.2)
    (fun a j ↦ cell (s a.1 j) a.2) (fun a ↦ cell (z a.1) a.2)
    (fun a j ↦ (square_iff_all_cells _ _ _).1 (hleg a.1 j) a.2)
    (fun a {_ _} t ↦ (square_iff_all_cells _ _ _).1 (hstage a.1 t) a.2)
    (fun a ↦ f a.1) (fun a ↦ (square_iff_all_cells _ _ _).1 (hf a.1) a.2)
  exact ⟨j, t, fun a ↦ (square_iff_all_cells _ _ _).2 (fun k ↦ ht (a, k))⟩

end DaggerTriangleWitnessStageEquations
