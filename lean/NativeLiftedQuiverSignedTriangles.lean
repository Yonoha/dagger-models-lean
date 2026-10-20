import NativeLiftedQuiverHeight

/-! Every signed lifted edge keeps the exact original groupoid triangle. -/
set_option autoImplicit false
open CategoryTheory
open DaggerNativeFreePathCompletionQuiverBridge DaggerNativePathUnitLiftedQuiver
open DaggerNativePathUnitQuiverCovering DaggerNativeLiftedQuiverHeight
open DaggerNativeFreeGroupoidWordLabels
universe u
namespace DaggerNativeLiftedQuiverSignedTriangles
noncomputable section

variable (V : Type u) [Quiver.{u + 1} V] (d : Quiver.FreeGroupoid V)

theorem signed_triangle {x y : Quiver.Symmetrify (Vertex V d)} (e : x ⟶ y) :
    x.hom ≫ (quotientMap V).map ((projection V d).symmetrify.map e).toPath = y.hom := by
  cases e with
  | inl e =>
    have h := e.property
    rw [path_unit_generator] at h
    exact h
  | inr e =>
    rcases e with ⟨e, h⟩
    rw [path_unit_generator] at h
    change x.hom ≫ (quotientMap V).map (Quiver.reverse e.toPos).toPath = y.hom
    rw [DaggerNativeSignedPathReduction.quotient_reverse_edge, ← h,
      Category.assoc, Groupoid.comp_inv, Category.comp_id]

theorem signed_projection_isCovering : (projection V d).symmetrify.IsCovering :=
  (projection_isCovering V d).symmetrify

end
end DaggerNativeLiftedQuiverSignedTriangles
