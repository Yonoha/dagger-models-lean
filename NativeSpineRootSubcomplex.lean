import NativeGeneratorSpineSimplices

/-! The actual root-generated subcomplex contains just the root among nondegenerate cells. -/
set_option autoImplicit false
open CategoryTheory Simplicial Opposite
open DaggerNativeGeneratorSpineSimplices
universe u
namespace DaggerNativeSpineRootSubcomplex
noncomputable section

variable {W : Type u} [Quiver.{u + 1} W] (r : W)

def rootComplex : (spine W).Subcomplex := SSet.Subcomplex.ofSimplex (vertex W r)

theorem vertex_mem_root_iff (x : W) : vertex W x ∈ (rootComplex r).obj (op ⦋0⦌) ↔ x = r := by
  constructor
  · rintro ⟨f, hf⟩
    have hc : (spine W).map f (vertex W r) = vertex W r := by
      apply Subtype.ext
      exact ComposableArrows.ext₀ rfl
    exact (vertex_injective W (hc.symm.trans hf)).symm
  · rintro rfl
    exact SSet.Subcomplex.mem_ofSimplex_obj _

theorem dimension_zero_of_nondegenerate_mem_root {n : ℕ} (s : (spine W) _⦋n⦌)
    (hs : s ∈ (spine W).nonDegenerate n) (hr : s ∈ (rootComplex r).obj (op ⦋n⦌)) : n = 0 := by
  obtain ⟨f, hf⟩ := hr
  have : Mono f.unop := (spine W).mono_of_nonDegenerate ⟨s, hs⟩ f.unop (vertex W r) hf
  have hd := SimplexCategory.len_le_of_mono f.unop
  change n ≤ 0 at hd
  omega

theorem edge_notMem_root {x y : W} (e : x ⟶ y) : edge W e ∉ (rootComplex r).obj _ := by
  intro he
  have hd := dimension_zero_of_nondegenerate_mem_root r (edge W e) (edge_nonDegenerate W e) he
  omega

end
end DaggerNativeSpineRootSubcomplex
