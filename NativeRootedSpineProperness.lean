import NativeRootedSpineCells
import NativeSpineRootSubcomplex

/-! The selected vertex is the unique codimension-one face of its actual parent edge. -/
set_option autoImplicit false
open CategoryTheory Simplicial Opposite
open DaggerNativeGeneratorSpineSimplices DaggerNativeRootedQuiverPairingData
open DaggerNativeRootedSpineCells DaggerNativeSpineRootSubcomplex
universe u
namespace DaggerNativeRootedSpineProperness
noncomputable section

variable {W : Type u} [Quiver.{u + 1} W] (D : Data W)

theorem upper_notMem_root (x : D.Cell) : upper D x ∉ (rootComplex D.root).obj _ := by
  rcases hp : D.parent x with ⟨y, e | e⟩ <;>
    simpa only [upper, hp] using edge_notMem_root D.root e

theorem vertex_notMem_root (x : D.Cell) : vertex W x.val ∉ (rootComplex D.root).obj _ := by
  intro he
  exact x.property ((vertex_mem_root_iff D.root x.val).mp he)

theorem unique_vertex_face (x : D.Cell) :
    SSet.IsUniquelyCodimOneFace (X := spine W) (vertex W x.val) (upper D x) := by
  have hne := D.parent_ne x
  rcases hp : D.parent x with ⟨y, e | e⟩
  · simp only [upper, hp]
    have hy : y ≠ x.val := by simpa only [hp] using hne
    apply SSet.IsUniquelyCodimOneFace.mk
    refine ⟨1, delta_one_edge W e, ?_⟩
    intro i hi
    fin_cases i
    · have hv := (delta_zero_edge W e).symm.trans hi
      exact (hy (vertex_injective W hv)).elim
    · rfl
  · simp only [upper, hp]
    have hy : y ≠ x.val := by simpa only [hp] using hne
    apply SSet.IsUniquelyCodimOneFace.mk
    refine ⟨0, delta_zero_edge W e, ?_⟩
    intro i hi
    fin_cases i
    · rfl
    · have hv := (delta_one_edge W e).symm.trans hi
      exact (hy (vertex_injective W hv)).elim

theorem face_height_lt {x y : D.Cell} (hne : x ≠ y)
    (hf : SSet.IsFace (X := spine W) (vertex W x.val) (upper D y)) :
    D.height x.val < D.height y.val := by
  obtain ⟨f, hm, _, he⟩ := hf
  have : Mono f := hm
  obtain ⟨i, rfl⟩ := SimplexCategory.eq_δ_of_mono f
  change (spine W).δ i (upper D y) = vertex W x.val at he
  have hh := D.parent_height y
  rcases hp : D.parent y with ⟨z, e | e⟩
  · simp only [upper, hp] at he
    have hy : D.height z + 1 = D.height y.val := by simpa only [hp] using hh
    fin_cases i
    · have hv := (delta_zero_edge W e).symm.trans he
      have hx := vertex_injective W hv
      rw [← hx]
      omega
    · have hv := (delta_one_edge W e).symm.trans he
      exact (hne (Subtype.ext (vertex_injective W hv).symm)).elim
  · simp only [upper, hp] at he
    have hy : D.height z + 1 = D.height y.val := by simpa only [hp] using hh
    fin_cases i
    · have hv := (delta_zero_edge W e).symm.trans he
      exact (hne (Subtype.ext (vertex_injective W hv).symm)).elim
    · have hv := (delta_one_edge W e).symm.trans he
      have hx := vertex_injective W hv
      rw [← hx]
      omega

end
end DaggerNativeRootedSpineProperness
