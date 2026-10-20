import NativeJoyalWeakInverseRecognition
import OriginalQuasicategoryPathTriangleWitnesses

/-!
# Native homotopy-category isomorphisms are witnessed by actual inverse triangles

Reuse the previously proved edge representability and exact triangle recognition
in the original path quotient. No alternative homotopy category replaces native ho.
-/
set_option autoImplicit false
open CategoryTheory Opposite Simplicial
open DaggerOriginalInnerHornFillers
open DaggerOriginalQuasicategoryPathEdgeRepresentatives
open DaggerOriginalQuasicategoryPathTriangleWitnesses
universe u
namespace DaggerNativeHoIsoTriangles
noncomputable section

theorem native_inner_fillers (X : SSet.{u}) [X.Quasicategory] : innerHornFillers X := by
  intro n i h0 hn σ₀
  exact SSet.Quasicategory.hornFilling h0 hn σ₀

/-- Two edges and their actual cancellation triangles, with the original vertices fixed. -/
structure IsoTriangles (X : SSet.{u}) (x y : SSet.hoFunctor.obj X) where
  forward : SSet.Edge (SSet.hoFunctor.obj.equiv X x) (SSet.hoFunctor.obj.equiv X y)
  backward : SSet.Edge (SSet.hoFunctor.obj.equiv X y) (SSet.hoFunctor.obj.equiv X x)
  leftTriangle : forward.CompStruct backward (SSet.Edge.id (SSet.hoFunctor.obj.equiv X x))
  rightTriangle : backward.CompStruct forward (SSet.Edge.id (SSet.hoFunctor.obj.equiv X y))

def IsoTriangles.toIso {X : SSet.{u}} {x y : SSet.hoFunctor.obj X}
    (d : IsoTriangles X x y) : x ≅ y where
  hom := SSet.Truncated.HomotopyCategory.homMk d.forward
  inv := SSet.Truncated.HomotopyCategory.homMk d.backward
  hom_inv_id := by
    exact (SSet.Truncated.HomotopyCategory.homMk_comp_homMk d.leftTriangle).trans
      (SSet.Truncated.HomotopyCategory.homMk_id _)
  inv_hom_id := by
    exact (SSet.Truncated.HomotopyCategory.homMk_comp_homMk d.rightTriangle).trans
      (SSet.Truncated.HomotopyCategory.homMk_id _)

def IsoTriangles.fromIso {X : SSet.{u}} [X.Quasicategory]
    {x y : SSet.hoFunctor.obj X} (e : x ≅ y) : IsoTriangles X x y := by
  have hX : innerHornFillers X := native_inner_fillers X
  let f := (original_homMk_surjective X hX e.hom).choose
  have hf : SSet.Truncated.HomotopyCategory.homMk f = e.hom :=
    (original_homMk_surjective X hX e.hom).choose_spec
  let g := (original_homMk_surjective X hX e.inv).choose
  have hg : SSet.Truncated.HomotopyCategory.homMk g = e.inv :=
    (original_homMk_surjective X hX e.inv).choose_spec
  refine ⟨f, g, ?_, ?_⟩
  · apply Nonempty.some
    apply (original_compStruct_iff_path_fac hX).mpr
    rw [hf, hg, e.hom_inv_id]
    exact (SSet.Truncated.HomotopyCategory.homMk_id _).symm
  · apply Nonempty.some
    apply (original_compStruct_iff_path_fac hX).mpr
    rw [hg, hf, e.inv_hom_id]
    exact (SSet.Truncated.HomotopyCategory.homMk_id _).symm

theorem iso_iff_triangles (X : SSet.{u}) [X.Quasicategory]
    (x y : SSet.hoFunctor.obj X) : Nonempty (x ≅ y) ↔ Nonempty (IsoTriangles X x y) :=
  ⟨fun ⟨e⟩ ↦ ⟨IsoTriangles.fromIso e⟩, fun ⟨d⟩ ↦ ⟨d.toIso⟩⟩

end
end DaggerNativeHoIsoTriangles
