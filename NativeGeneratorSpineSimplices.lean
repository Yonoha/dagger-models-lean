import NativeFreePathGeneratorComplex
import TopCatModelCategory.SSet.PairingCore

/-! The actual generator spine has exactly vertices and generating edges as nondegenerate cells. -/
set_option autoImplicit false
open CategoryTheory Simplicial Opposite
open DaggerNativeFreePathGeneratorComplex DaggerNativeFreePathNerveWeight
open DaggerNativeFreePathInnerFaceNondegeneracy DaggerNativeFreePathSubdivisionInverse
universe u
namespace DaggerNativeGeneratorSpineSimplices
noncomputable section

variable (W : Type u) [Quiver.{u + 1} W]

abbrev spine : SSet.{u} := (generatorComplex W).toSSet

def vertex (x : W) : (spine W) _⦋0⦌ := ⟨ComposableArrows.mk₀ x, vertex_mem_generatorComplex x⟩

def edge {x y : W} (e : x ⟶ y) : (spine W) _⦋1⦌ :=
  ⟨ComposableArrows.mk₁ e.toPath, edge_mem_generatorComplex e⟩

theorem vertex_injective : Function.Injective (vertex W) := by
  intro x y h
  exact congrArg (fun z : (spine W) _⦋0⦌ ↦ z.val.obj 0) h

theorem vertex_surjective (s : (spine W) _⦋0⦌) : ∃ x : W, s = vertex W x := by
  obtain ⟨x, hx⟩ := ComposableArrows.mk₀_surjective s.val
  exact ⟨x, Subtype.ext hx⟩

theorem delta_zero_edge {x y : W} (e : x ⟶ y) :
    (spine W).δ (0 : Fin 2) (edge W e) = vertex W y := by
  apply Subtype.ext
  exact ComposableArrows.ext₀ rfl

theorem delta_one_edge {x y : W} (e : x ⟶ y) :
    (spine W).δ (1 : Fin 2) (edge W e) = vertex W x := by
  apply Subtype.ext
  exact ComposableArrows.ext₀ rfl

theorem vertex_nonDegenerate (x : W) : vertex W x ∈ (spine W).nonDegenerate 0 := by simp

theorem edge_nonDegenerate {x y : W} (e : x ⟶ y) :
    edge W e ∈ (spine W).nonDegenerate 1 := by
  apply ((generatorComplex W).mem_nonDegenerate_iff (edge W e)).mpr
  apply (nonDegenerate_iff_front (ComposableArrows.mk₁ e.toPath)).mpr
  exact ⟨Nat.zero_lt_succ 0, by simp⟩

theorem nonDegenerate_dimension_le_one {n : ℕ} (s : (spine W) _⦋n⦌)
    (hs : s ∈ (spine W).nonDegenerate n) : n ≤ 1 := by
  have hn := ((generatorComplex W).mem_nonDegenerate_iff s).mp hs
  have hd := dimension_le_weight s.val hn
  have hw := generatorComplex_le_spine (V := W) _ s.property
  change weight s.val ≤ 1 at hw
  exact hd.trans hw

theorem edge_surjective (s : (spine W) _⦋1⦌) (hs : s ∈ (spine W).nonDegenerate 1) :
    ∃ (x y : W) (e : x ⟶ y), s = edge W e := by
  have hn := ((generatorComplex W).mem_nonDegenerate_iff s).mp hs
  have hp : 0 < s.val.hom.length := ((nonDegenerate_iff_front s.val).mp hn).1
  have hw := generatorComplex_le_spine (V := W) _ s.property
  change s.val.hom.length ≤ 1 at hw
  obtain ⟨e, he⟩ := path_eq_generator_of_length_one (V := W) s.val.hom (by omega)
  refine ⟨s.val.left, s.val.right, e, Subtype.ext ?_⟩
  exact (congrArg ComposableArrows.mk₁ he).trans (ComposableArrows.mk₁_hom s.val) |>.symm

end
end DaggerNativeGeneratorSpineSimplices
