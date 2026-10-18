import OriginalFullVertexSubcomplexUniversal
import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal

/-!
# Strict-endpoint cylinders factor through a full vertex subcomplex

The two endpoint conditions on a simplicial cylinder determine every vertex
of the cylinder. Thus any such cylinder factors uniquely through the full
subcomplex spanned by a vertex set containing its endpoints.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial MonoidalCategory

universe u

namespace DaggerOriginalFullVertexSubcomplex

noncomputable section

/-- The exact factorization of a cylinder with pointwise constant endpoints. -/
def strictEndpointCylinderLift {Z X : SSet.{u}}
    (V : Set (X.obj (op ⦋0⦌)))
    (a b : X.obj (op ⦋0⦌)) (ha : a ∈ V) (hb : b ∈ V)
    (f : Δ[1] ⊗ Z ⟶ X)
    (h₀ : ∀ z : Z.obj (op ⦋0⦌),
      f.app (op ⦋0⦌) ⟨SSet.stdSimplex.obj₀Equiv.symm 0, z⟩ = a)
    (h₁ : ∀ z : Z.obj (op ⦋0⦌),
      f.app (op ⦋0⦌) ⟨SSet.stdSimplex.obj₀Equiv.symm 1, z⟩ = b) :
    Δ[1] ⊗ Z ⟶ (fullVertexSubcomplex X V : SSet) :=
  liftMapOfVertices V f (by
    rintro ⟨e, z⟩
    let k : Fin 2 := SSet.stdSimplex.obj₀Equiv e
    have he : e = SSet.stdSimplex.obj₀Equiv.symm k :=
      (SSet.stdSimplex.obj₀Equiv.symm_apply_apply e).symm
    have hk : k = 0 ∨ k = 1 := by omega
    rcases hk with hk | hk
    · simpa only [he, hk, h₀ z] using ha
    · simpa only [he, hk, h₁ z] using hb)

@[reassoc (attr := simp)]
theorem strictEndpointCylinderLift_ι {Z X : SSet.{u}}
    (V : Set (X.obj (op ⦋0⦌))) (a b : X.obj (op ⦋0⦌))
    (ha : a ∈ V) (hb : b ∈ V) (f : Δ[1] ⊗ Z ⟶ X)
    (h₀ : ∀ z : Z.obj (op ⦋0⦌),
      f.app (op ⦋0⦌) ⟨SSet.stdSimplex.obj₀Equiv.symm 0, z⟩ = a)
    (h₁ : ∀ z : Z.obj (op ⦋0⦌),
      f.app (op ⦋0⦌) ⟨SSet.stdSimplex.obj₀Equiv.symm 1, z⟩ = b) :
    strictEndpointCylinderLift V a b ha hb f h₀ h₁ ≫
      (fullVertexSubcomplex X V).ι = f :=
  liftMapOfVertices_ι V f _

end

end DaggerOriginalFullVertexSubcomplex
