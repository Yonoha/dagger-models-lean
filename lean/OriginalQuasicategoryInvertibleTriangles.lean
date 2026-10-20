import OriginalQuasicategoryPathTriangleWitnesses

/-!
# Actual inverse and outer triangles for original invertible edges

Represent inverse and cancellation arrows in the same original path quotient,
then use the proved original path equation / triangle correspondence. Every
result is an actual CompStruct in the original input, with fixed endpoints and
original unit invertibility. No outer-horn premise is added.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial
open DaggerOriginalOrdinaryKanCoreEdgeMembership
open DaggerOriginalInnerHornFillers
open DaggerOriginalQuasicategoryPathEdgeRepresentatives
open DaggerOriginalQuasicategoryInverseEdgeRepresentatives
open DaggerOriginalQuasicategoryPathTriangleWitnesses

universe u

namespace DaggerOriginalQuasicategoryInvertibleTriangles

noncomputable section

/-- A reversed original edge admits actual left and right inverse triangles in the same input. -/
theorem inverse_triangles {X : SSet.{u}} (hX : innerHornFillers X)
    {x y : X.obj (op ⦋0⦌)} (e : SSet.Edge x y) (he : edgeIsInvertible X e.edge) :
    ∃ r : SSet.Edge y x, Nonempty (e.CompStruct r (SSet.Edge.id x)) ∧
      Nonempty (r.CompStruct e (SSet.Edge.id y)) ∧ edgeIsInvertible X r.edge := by
  obtain ⟨r, her, hre, hr⟩ := original_inverse_edge X hX e he
  have hidₓ : SSet.Truncated.HomotopyCategory.homMk (SSet.Edge.id x) = 𝟙 _ :=
    SSet.Truncated.HomotopyCategory.homMk_id (V := (SSet.truncation 2).obj X) x
  have hidᵧ : SSet.Truncated.HomotopyCategory.homMk (SSet.Edge.id y) = 𝟙 _ :=
    SSet.Truncated.HomotopyCategory.homMk_id (V := (SSet.truncation 2).obj X) y
  exact ⟨r, (original_compStruct_iff_path_fac hX).mpr (her.trans hidₓ.symm),
    (original_compStruct_iff_path_fac hX).mpr (hre.trans hidᵧ.symm), hr⟩

/-- An invertible first side and diagonal complete an actual original outer triangle. -/
theorem complete_triangle_left {X : SSet.{u}} (hX : innerHornFillers X)
    {x y z : X.obj (op ⦋0⦌)} (f : SSet.Edge x y) (h : SSet.Edge x z)
    (hf : edgeIsInvertible X f.edge) (hh : edgeIsInvertible X h.edge) :
    ∃ g : SSet.Edge y z, Nonempty (f.CompStruct g h) ∧ edgeIsInvertible X g.edge := by
  have : IsIso (SSet.Truncated.HomotopyCategory.homMk f) :=
    (edgeIsInvertible_iff_original_homMk_isIso X f).mp hf
  have : IsIso (SSet.Truncated.HomotopyCategory.homMk h) :=
    (edgeIsInvertible_iff_original_homMk_isIso X h).mp hh
  obtain ⟨g, hg⟩ := original_homMk_surjective X hX
    (inv (SSet.Truncated.HomotopyCategory.homMk f) ≫
      SSet.Truncated.HomotopyCategory.homMk h)
  have hfac : SSet.Truncated.HomotopyCategory.homMk f ≫
      SSet.Truncated.HomotopyCategory.homMk g =
        SSet.Truncated.HomotopyCategory.homMk h := by
    rw [hg, ← Category.assoc, IsIso.hom_inv_id]
    exact Category.id_comp _
  refine ⟨g, (original_compStruct_iff_path_fac hX).mpr hfac, ?_⟩
  apply (edgeIsInvertible_iff_original_homMk_isIso X g).mpr
  rw [hg]
  infer_instance

/-- An invertible last side and diagonal complete an actual original outer triangle. -/
theorem complete_triangle_right {X : SSet.{u}} (hX : innerHornFillers X)
    {x y z : X.obj (op ⦋0⦌)} (g : SSet.Edge y z) (h : SSet.Edge x z)
    (hg : edgeIsInvertible X g.edge) (hh : edgeIsInvertible X h.edge) :
    ∃ f : SSet.Edge x y, Nonempty (f.CompStruct g h) ∧ edgeIsInvertible X f.edge := by
  have : IsIso (SSet.Truncated.HomotopyCategory.homMk g) :=
    (edgeIsInvertible_iff_original_homMk_isIso X g).mp hg
  have : IsIso (SSet.Truncated.HomotopyCategory.homMk h) :=
    (edgeIsInvertible_iff_original_homMk_isIso X h).mp hh
  obtain ⟨f, hf⟩ := original_homMk_surjective X hX
    (SSet.Truncated.HomotopyCategory.homMk h ≫
      inv (SSet.Truncated.HomotopyCategory.homMk g))
  have hfac : SSet.Truncated.HomotopyCategory.homMk f ≫
      SSet.Truncated.HomotopyCategory.homMk g =
        SSet.Truncated.HomotopyCategory.homMk h := by
    rw [hf, Category.assoc, IsIso.inv_hom_id]
    exact Category.comp_id _
  refine ⟨f, (original_compStruct_iff_path_fac hX).mpr hfac, ?_⟩
  apply (edgeIsInvertible_iff_original_homMk_isIso X f).mpr
  rw [hf]
  infer_instance

end

end DaggerOriginalQuasicategoryInvertibleTriangles
