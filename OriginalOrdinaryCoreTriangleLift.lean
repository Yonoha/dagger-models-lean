import OriginalOrdinaryCorePathGroupoid

/-!
# Actual composition triangles lift to the same original core

Given three literal edges of the original core and an actual composition
triangle between their images in the input, the native inner two-horn pushout
and the proved filler-membership theorem retain that very triangle in the core.
The returned triangle has the same underlying simplex and the same three edges.
No Kan or higher outer-horn filler is assumed.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial
open DaggerOriginalOrdinaryKanCoreSubcomplex
open DaggerOriginalOrdinaryKanCoreKanInverseEdges
open DaggerOriginalQuasicategoryComposeEdges
open DaggerOriginalOrdinaryCoreHornFillerMembership

universe u

namespace DaggerOriginalOrdinaryCoreTriangleLift

noncomputable section

/-- An actual triangle between images of original core edges belongs to that same core. -/
theorem core_triangle_mem (X : SSet.{u})
    {x y z : (ordinaryCoreCandidate X : SSet.{u}).obj (op ⦋0⦌)}
    {e : SSet.Edge x y} {f : SSet.Edge y z} {g : SSet.Edge x z}
    (t : (e.map (ordinaryCoreCandidate X).ι).CompStruct
      (f.map (ordinaryCoreCandidate X).ι) (g.map (ordinaryCoreCandidate X).ι)) :
    t.simplex ∈ (ordinaryCoreCandidate X).obj (op ⦋2⦌) := by
  let a : (Δ[1] : SSet.{u}) ⟶ (ordinaryCoreCandidate X : SSet.{u}) :=
    SSet.yonedaEquiv.symm e.edge
  let b : (Δ[1] : SSet.{u}) ⟶ (ordinaryCoreCandidate X : SSet.{u}) :=
    SSet.yonedaEquiv.symm f.edge
  have w : SSet.stdSimplex.δ 0 ≫ a = SSet.stdSimplex.δ 1 ≫ b := by
    apply SSet.yonedaEquiv.injective
    rw [yonedaEquiv_coface, yonedaEquiv_coface]
    simp only [a, b, Equiv.apply_symm_apply, e.tgt_eq, f.src_eq]
  let φ := SSet.horn₂₁.isPushout.desc a b w
  let μ : (Δ[2] : SSet.{u}) ⟶ X := SSet.yonedaEquiv.symm t.simplex
  have h01 : SSet.stdSimplex.δ 2 ≫ μ = a ≫ (ordinaryCoreCandidate X).ι := by
    apply SSet.yonedaEquiv.injective
    rw [yonedaEquiv_coface, SSet.yonedaEquiv_comp]
    change X.δ 2 (SSet.yonedaEquiv (SSet.yonedaEquiv.symm t.simplex)) =
      (ordinaryCoreCandidate X).ι.app (op ⦋1⦌)
        (SSet.yonedaEquiv (SSet.yonedaEquiv.symm e.edge))
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    exact t.d₂
  have h12 : SSet.stdSimplex.δ 0 ≫ μ = b ≫ (ordinaryCoreCandidate X).ι := by
    apply SSet.yonedaEquiv.injective
    rw [yonedaEquiv_coface, SSet.yonedaEquiv_comp]
    change X.δ 0 (SSet.yonedaEquiv (SSet.yonedaEquiv.symm t.simplex)) =
      (ordinaryCoreCandidate X).ι.app (op ⦋1⦌)
        (SSet.yonedaEquiv (SSet.yonedaEquiv.symm f.edge))
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    exact t.d₀
  have hφ : φ ≫ (ordinaryCoreCandidate X).ι = Λ[2, 1].ι ≫ μ := by
    apply SSet.horn₂₁.isPushout.hom_ext
    · rw [← Category.assoc, SSet.horn₂₁.isPushout.inl_desc, ← Category.assoc,
        horn₁_inl_comp]
      exact h01.symm
    · rw [← Category.assoc, SSet.horn₂₁.isPushout.inr_desc, ← Category.assoc,
        horn₁_inr_comp]
      exact h12.symm
  simpa only [μ, Equiv.apply_symm_apply] using core_twoHorn_filler_mem X φ μ hφ

/-- The exact original triangle lifts with its underlying simplex unchanged. -/
def liftCoreTriangle (X : SSet.{u})
    {x y z : (ordinaryCoreCandidate X : SSet.{u}).obj (op ⦋0⦌)}
    {e : SSet.Edge x y} {f : SSet.Edge y z} {g : SSet.Edge x z}
    (t : (e.map (ordinaryCoreCandidate X).ι).CompStruct
      (f.map (ordinaryCoreCandidate X).ι) (g.map (ordinaryCoreCandidate X).ι)) :
    e.CompStruct f g :=
  SSet.Edge.CompStruct.mk ⟨t.simplex, core_triangle_mem X t⟩
    (by apply Subtype.ext; exact t.d₂)
    (by apply Subtype.ext; exact t.d₀)
    (by apply Subtype.ext; exact t.d₁)

/-- The lifted triangle followed by the actual inclusion retains the original simplex. -/
theorem liftCoreTriangle_simplex (X : SSet.{u})
    {x y z : (ordinaryCoreCandidate X : SSet.{u}).obj (op ⦋0⦌)}
    {e : SSet.Edge x y} {f : SSet.Edge y z} {g : SSet.Edge x z}
    (t : (e.map (ordinaryCoreCandidate X).ι).CompStruct
      (f.map (ordinaryCoreCandidate X).ι) (g.map (ordinaryCoreCandidate X).ι)) :
    (ordinaryCoreCandidate X).ι.app (op ⦋2⦌) (liftCoreTriangle X t).simplex = t.simplex :=
  rfl

end

end DaggerOriginalOrdinaryCoreTriangleLift
