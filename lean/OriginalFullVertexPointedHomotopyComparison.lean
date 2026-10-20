import OriginalFullVertexPointedSimplexComparison
import TopCatModelCategory.SSet.FundamentalGroupoidPiOne

/-!
# Original relative homotopies in a full vertex subcomplex

A cylinder whose endpoint maps land in the original full subcomplex has
all vertices in the same selected set. The literal relative homotopy
therefore factors through the inclusion. This proves injectivity on the
native homotopy classes in every degree and bijectivity in positive degrees.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial MonoidalCategory HomotopicalAlgebra
open DaggerOriginalFullVertexSubcomplex DaggerOriginalFullVertexPointedSimplexComparison
open scoped SSet.modelCategoryQuillen

universe u

namespace DaggerOriginalFullVertexPointedHomotopyComparison

noncomputable section

/-- An actual vertex of the original full subcomplex is in its selected vertex set. -/
theorem fullVertex_vertex_mem {X : SSet.{u}} (V : Set (X _⦋0⦌))
    (a : (fullVertexSubcomplex X V : SSet.{u}) _⦋0⦌) : a.val ∈ V := by
  have h := a.property (𝟙 ⦋0⦌)
  simpa using h

/-- The original cylinder factors when its two endpoint maps land in the full subcomplex. -/
def endpointCylinderLift {X Z : SSet.{u}} (V : Set (X _⦋0⦌))
    (f g : Z ⟶ (fullVertexSubcomplex X V : SSet.{u})) (h : Z ⊗ Δ[1] ⟶ X)
    (h₀ : SSet.ι₀ ≫ h = f ≫ (fullVertexSubcomplex X V).ι)
    (h₁ : SSet.ι₁ ≫ h = g ≫ (fullVertexSubcomplex X V).ι) :
    Z ⊗ Δ[1] ⟶ (fullVertexSubcomplex X V : SSet.{u}) :=
  liftMapOfVertices V h (by
    rintro ⟨z, e⟩
    let k : Fin 2 := SSet.stdSimplex.obj₀Equiv e
    have he : e = SSet.stdSimplex.obj₀Equiv.symm k :=
      (SSet.stdSimplex.obj₀Equiv.symm_apply_apply e).symm
    have hk : k = 0 ∨ k = 1 := by omega
    rcases hk with hk | hk
    · have hp := congrArg (fun t : Z ⟶ X ↦ t.app (op ⦋0⦌) z) h₀
      change h.app (op ⦋0⦌) (z, SSet.stdSimplex.obj₀Equiv.symm 0) =
        (f.app (op ⦋0⦌) z).val at hp
      simpa only [he, hk, hp] using fullVertex_vertex_mem V (f.app (op ⦋0⦌) z)
    · have hp := congrArg (fun t : Z ⟶ X ↦ t.app (op ⦋0⦌) z) h₁
      change h.app (op ⦋0⦌) (z, SSet.stdSimplex.obj₀Equiv.symm 1) =
        (g.app (op ⦋0⦌) z).val at hp
      simpa only [he, hk, hp] using fullVertex_vertex_mem V (g.app (op ⦋0⦌) z))

/-- Inclusion of the cylinder lift is its original ambient map. -/
theorem endpointCylinderLift_ι {X Z : SSet.{u}} (V : Set (X _⦋0⦌))
    (f g : Z ⟶ (fullVertexSubcomplex X V : SSet.{u})) (h : Z ⊗ Δ[1] ⟶ X)
    (h₀ : SSet.ι₀ ≫ h = f ≫ (fullVertexSubcomplex X V).ι)
    (h₁ : SSet.ι₁ ≫ h = g ≫ (fullVertexSubcomplex X V).ι) :
    endpointCylinderLift V f g h h₀ h₁ ≫ (fullVertexSubcomplex X V).ι = h :=
  liftMapOfVertices_ι V h _

variable {X : SSet.{u}} (V : Set (X _⦋0⦌))
variable (a : (fullVertexSubcomplex X V : SSet.{u}) _⦋0⦌)

/-- The same original pointed homotopy factors with its boundary condition unchanged. -/
def pointedHomotopyLift {n : ℕ}
    (p q : (fullVertexSubcomplex X V : SSet.{u}).PtSimplex n a)
    (h : (p.pushforward (fullVertexSubcomplex X V).ι a.val rfl).Homotopy
      (q.pushforward (fullVertexSubcomplex X V).ι a.val rfl)) : p.Homotopy q where
  h := endpointCylinderLift V p.map q.map h.h h.h₀ h.h₁
  h₀ := by
    apply (cancel_mono (fullVertexSubcomplex X V).ι).mp
    rw [Category.assoc, endpointCylinderLift_ι]
    exact h.h₀
  h₁ := by
    apply (cancel_mono (fullVertexSubcomplex X V).ι).mp
    rw [Category.assoc, endpointCylinderLift_ι]
    exact h.h₁
  rel := by
    apply (cancel_mono (fullVertexSubcomplex X V).ι).mp
    rw [Category.assoc, endpointCylinderLift_ι]
    simpa only [Category.assoc, SSet.Subcomplex.ofSimplex_ι,
      SSet.const_comp, SSet.comp_const] using h.rel

/-- The actual inclusion is injective on native pointed homotopy classes in every degree. -/
theorem inclusion_mapπ_injective [SSet.KanComplex X] (n : ℕ) :
    Function.Injective (SSet.KanComplex.mapπ (fullVertexSubcomplex X V).ι n a a.val rfl) := by
  intro p q h
  obtain ⟨p, rfl⟩ := SSet.KanComplex.π.mk_surjective p
  obtain ⟨q, rfl⟩ := SSet.KanComplex.π.mk_surjective q
  obtain ⟨h⟩ := (SSet.KanComplex.π.mk_eq_mk_iff).1 h
  exact (SSet.KanComplex.π.mk_eq_mk_iff).2
    ⟨(pointedHomotopyLift V a p q h.homotopy).relStruct₀⟩

/-- The actual inclusion is bijective on native positive pointed homotopy classes. -/
theorem inclusion_mapπ_positive_bijective [SSet.KanComplex X] (n : ℕ) :
    Function.Bijective
      (SSet.KanComplex.mapπ (fullVertexSubcomplex X V).ι (n + 1) a a.val rfl) := by
  refine ⟨inclusion_mapπ_injective V a _, ?_⟩
  intro p
  obtain ⟨p, rfl⟩ := SSet.KanComplex.π.mk_surjective p
  refine ⟨SSet.KanComplex.π.mk (pointedSimplexLift V a p), ?_⟩
  rw [SSet.KanComplex.mapπ_mk, pointedSimplexLift_pushforward]

end

end DaggerOriginalFullVertexPointedHomotopyComparison
