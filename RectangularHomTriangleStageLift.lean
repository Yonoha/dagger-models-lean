import IsoTriangleFilteredStageLift
import PresentableParameterIhomAccessibility
import RawIsoTriangleCasts

/-! All chosen triangles between whole maps from a presentable domain lift exactly. -/
set_option autoImplicit false
open CategoryTheory Limits Opposite Simplicial
open DaggerNativeHoIsoTriangles DaggerNativeIhomHoObjects
open DaggerRawIsoTriangleCells DaggerInverseTriangleCellFamily
universe u
namespace DaggerRectangularHomTriangleStageLift
noncomputable section

theorem post_vertex {A B Z : SSet.{u}} (f : A ⟶ B) (g : B ⟶ Z) :
    (SSet.hoFunctor.obj.equiv ((ihom A).obj Z)).symm
      (((ihom A).map g).app (op ⦋0⦌)
        (SSet.hoFunctor.obj.equiv ((ihom A).obj B) (homObject f))) = homObject (f ≫ g) := by
  apply (SSet.hoFunctor.obj.equiv _).injective
  rw [Equiv.apply_symm_apply, ← post_obj f g, postHoFunctor, ho_map_obj]

theorem lift (κ : Cardinal.{u}) [Fact κ.IsRegular]
    {J : Type u} [SmallCategory J] [IsCardinalFiltered J κ]
    {F : J ⥤ SSet.{u}} {c : Cocone F} (hc : IsColimit c)
    (A : SSet.{u}) [IsCardinalPresentable A κ] (h k : A ⟶ c.pt)
    (d : IsoTriangles ((ihom A).obj c.pt) (homObject h) (homObject k))
    (i : J) (hi ki : A ⟶ F.obj i) (hh : hi ≫ c.ι.app i = h) (hk : ki ≫ c.ι.app i = k) :
    ∃ (j : J) (t : i ⟶ j)
      (e : IsoTriangles ((ihom A).obj (F.obj j))
        (homObject (hi ≫ F.map t)) (homObject (ki ≫ F.map t))),
      ∀ r : Kind, ((ihom A).map (c.ι.app j)).app (op ⦋r.degree⦌) (cell e r) = cell d r := by
  have : (ihom A).IsCardinalAccessible κ :=
    DaggerPresentableParameterIhomAccessibility.accessible κ A
  have : PreservesColimitsOfShape J (ihom A) :=
    Functor.preservesColimitsOfShape_of_isCardinalAccessible (ihom A) κ J
  have hhi : ((ihom A).map (c.ι.app i)).app (op ⦋0⦌)
      (SSet.hoFunctor.obj.equiv ((ihom A).obj (F.obj i)) (homObject hi)) =
        SSet.hoFunctor.obj.equiv ((ihom A).obj c.pt) (homObject h) := by
    rw [← hh, ← post_obj hi (c.ι.app i), postHoFunctor, ho_map_obj]
  have hki : ((ihom A).map (c.ι.app i)).app (op ⦋0⦌)
      (SSet.hoFunctor.obj.equiv ((ihom A).obj (F.obj i)) (homObject ki)) =
        SSet.hoFunctor.obj.equiv ((ihom A).obj c.pt) (homObject k) := by
    rw [← hk, ← post_obj ki (c.ι.app i), postHoFunctor, ho_map_obj]
  obtain ⟨j, t, e, he⟩ := DaggerIsoTriangleFilteredStageLift.lift κ
    (isColimitOfPreserves (ihom A) hc) d i
    (SSet.hoFunctor.obj.equiv ((ihom A).obj (F.obj i)) (homObject hi))
    (SSet.hoFunctor.obj.equiv ((ihom A).obj (F.obj i)) (homObject ki)) hhi hki
  let e' := DaggerNativeIsoTriangleCellTransport.cast
    (post_vertex hi (F.map t)) (post_vertex ki (F.map t)) e
  refine ⟨j, t, e', fun r ↦ ?_⟩
  dsimp [e']
  rw [DaggerRawIsoTriangleCasts.cell_cast]
  exact he r

end
end DaggerRectangularHomTriangleStageLift
