import NativeKanSourceOriginalCoreFactor

/-! All native homotopy-category arrows of a Kan complex are invertible. -/
set_option autoImplicit false
open CategoryTheory Opposite Simplicial
open SSet.Truncated.HomotopyCategory
open DaggerNativeHoIsoTriangles DaggerOriginalQuasicategoryPathEdgeRepresentatives
open DaggerOriginalOrdinaryKanCoreKanInverseEdges
universe u
namespace DaggerNativeKanHomotopyCategoryGroupoid
noncomputable section

theorem homMk_isIso {K : SSet.{u}} [K.KanComplex] {x y : K _⦋0⦌}
    (e : SSet.Edge x y) : IsIso (homMk e) := by
  obtain ⟨r, ⟨hr⟩⟩ := kan_right_inverse_edge e
  obtain ⟨s, ⟨hs⟩⟩ := kan_right_inverse_edge r
  have hfg : homMk e ≫ homMk r = 𝟙 _ :=
    (homMk_comp_homMk hr).trans (homMk_id _)
  have hgk : homMk r ≫ homMk s = 𝟙 _ :=
    (homMk_comp_homMk hs).trans (homMk_id _)
  have hfk : homMk e = homMk s := by
    calc
      homMk e = homMk e ≫ 𝟙 _ := (Category.comp_id _).symm
      _ = homMk e ≫ (homMk r ≫ homMk s) := congrArg (homMk e ≫ ·) hgk.symm
      _ = (homMk e ≫ homMk r) ≫ homMk s := (Category.assoc _ _ _).symm
      _ = homMk s := by rw [hfg, Category.id_comp]
  refine ⟨⟨homMk r, hfg, ?_⟩⟩
  rw [hfk]
  exact hgk

theorem ho_isIso (K : SSet.{u}) [K.KanComplex]
    {x y : SSet.hoFunctor.obj K} (f : x ⟶ y) : IsIso f := by
  obtain ⟨e, rfl⟩ := original_homMk_surjective K (native_inner_fillers K) f
  exact homMk_isIso e

end
end DaggerNativeKanHomotopyCategoryGroupoid
