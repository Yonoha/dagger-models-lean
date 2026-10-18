import IsoTriangleFiniteEquations
import FiniteStageHomFactors
import NativeEndomorphismSimplexMaps

/-!
# Every chosen inverse-triangle datum lifts to a later filtered stage

The two prescribed vertex values and all four original raw cells are preserved
exactly by the original cocone leg. No quasi-category assumption is required.
-/
set_option autoImplicit false
open CategoryTheory Limits Opposite Simplicial
open DaggerNativeHoIsoTriangles DaggerInverseTriangleCellFamily DaggerRawIsoTriangleCells
open DaggerIsoTriangleFiniteEquations
universe u
namespace DaggerIsoTriangleFilteredStageLift
noncomputable section
attribute [local instance] Cardinal.fact_isRegular_aleph0

theorem deltaPresentable (κ : Cardinal.{u}) [hκ : Fact κ.IsRegular] (n : ℕ) :
    IsCardinalPresentable (Δ[n] : SSet.{u}) κ :=
  isCardinalPresentable_of_le Δ[n] hκ.out.aleph0_le

theorem lift (κ : Cardinal.{u}) [Fact κ.IsRegular]
    {J : Type u} [SmallCategory J] [IsCardinalFiltered J κ]
    {F : J ⥤ SSet.{u}} {c : Cocone F} (hc : IsColimit c)
    {x y : SSet.hoFunctor.obj c.pt} (d : IsoTriangles c.pt x y)
    (i : J) (xi yi : (F.obj i).obj (op ⦋0⦌))
    (hx : (c.ι.app i).app (op ⦋0⦌) xi = SSet.hoFunctor.obj.equiv c.pt x)
    (hy : (c.ι.app i).app (op ⦋0⦌) yi = SSet.hoFunctor.obj.equiv c.pt y) :
    ∃ (j : J) (t : i ⟶ j)
      (e : IsoTriangles (F.obj j)
        ((SSet.hoFunctor.obj.equiv (F.obj j)).symm ((F.map t).app (op ⦋0⦌) xi))
        ((SSet.hoFunctor.obj.equiv (F.obj j)).symm ((F.map t).app (op ⦋0⦌) yi))),
      ∀ r : Kind, (c.ι.app j).app (op ⦋r.degree⦌) (cell e r) = cell d r := by
  let K : ULift.{u} Kind → SSet.{u} := fun a ↦ Δ[a.down.degree]
  let D : ULift.{u} Kind → J ⥤ SSet.{u} := fun _ ↦ F
  let cc : ∀ a, Cocone (D a) := fun _ ↦ c
  let f : ∀ a, K a ⟶ (cc a).pt := fun a ↦ SSet.yonedaEquiv.symm (cell d a.down)
  obtain ⟨j, t, g, hg⟩ := DaggerFiniteStageHomFactors.all_homs κ K D cc
    (fun _ ↦ hc) (fun a ↦ deltaPresentable κ a.down.degree) f i
  let s : ∀ r : Kind, (F.obj j).obj (op ⦋r.degree⦌) :=
    fun r ↦ SSet.yonedaEquiv (g (ULift.up r))
  have hf : ∀ r, (c.ι.app j).app (op ⦋r.degree⦌) (s r) = cell d r := by
    intro r
    have h := congrArg SSet.yonedaEquiv (hg (ULift.up r))
    have hh : (c.ι.app j).app (op ⦋r.degree⦌) (s r) =
        SSet.yonedaEquiv (SSet.yonedaEquiv.symm (cell d r)) := by
      simpa only [cc, s, f, SSet.yonedaEquiv_comp] using h
    exact hh.trans (SSet.yonedaEquiv.apply_symm_apply (cell d r))
  let vx := (F.map t).app (op ⦋0⦌) xi
  let vy := (F.map t).app (op ⦋0⦌) yi
  have hxj : (c.ι.app j).app (op ⦋0⦌) vx = SSet.hoFunctor.obj.equiv c.pt x := by
    exact (congrArg (fun f : F.obj i ⟶ c.pt ↦ f.app (op ⦋0⦌) xi) (c.w t)).trans hx
  have hyj : (c.ι.app j).app (op ⦋0⦌) vy = SSet.hoFunctor.obj.equiv c.pt y := by
    exact (congrArg (fun f : F.obj i ⟶ c.pt ↦ f.app (op ⦋0⦌) yi) (c.w t)).trans hy
  have hs : (fun r ↦ (c.ι.app j).app (op ⦋r.degree⦌) (s r)) = cell d := funext hf
  have he : ∀ r : EquationKind,
      (c.ι.app j).app (op ⦋r.degree⦌) (lhs (F.obj j) s r) =
        (c.ι.app j).app (op ⦋r.degree⦌) (rhs (F.obj j) s vx vy r) := by
    intro r
    rw [lhs_map, rhs_map, hs, hxj, hyj]
    exact original_equations c.pt d r
  let KE : ULift.{u} EquationKind → SSet.{u} := fun r ↦ Δ[r.down.degree]
  let DE : ULift.{u} EquationKind → J ⥤ SSet.{u} := fun _ ↦ F
  let ce : ∀ r, Cocone (DE r) := fun _ ↦ c
  let a : ∀ r, KE r ⟶ (DE r).obj j :=
    fun r ↦ SSet.yonedaEquiv.symm (lhs (F.obj j) s r.down)
  let b : ∀ r, KE r ⟶ (DE r).obj j :=
    fun r ↦ SSet.yonedaEquiv.symm (rhs (F.obj j) s vx vy r.down)
  have he' : ∀ r, a r ≫ (ce r).ι.app j = b r ≫ (ce r).ι.app j := by
    intro r
    apply SSet.yonedaEquiv.injective
    simpa only [ce, a, b, SSet.yonedaEquiv_comp, Equiv.apply_symm_apply] using he r.down
  obtain ⟨k, v, hv⟩ := DaggerFiniteStageEquations.all_equations κ KE DE ce
    (fun _ ↦ hc) (fun r ↦ deltaPresentable κ r.down.degree) a b he'
  let ss : ∀ r : Kind, (F.obj k).obj (op ⦋r.degree⦌) :=
    fun r ↦ (F.map v).app (op ⦋r.degree⦌) (s r)
  let xx := (F.map v).app (op ⦋0⦌) vx
  let yy := (F.map v).app (op ⦋0⦌) vy
  have hss : ∀ r : EquationKind, lhs (F.obj k) ss r = rhs (F.obj k) ss xx yy r := by
    intro r
    have hh := congrArg SSet.yonedaEquiv (hv (ULift.up r))
    have hh' : (F.map v).app (op ⦋r.degree⦌) (lhs (F.obj j) s r) =
        (F.map v).app (op ⦋r.degree⦌) (rhs (F.obj j) s vx vy r) := by
      simpa only [DE, a, b, SSet.yonedaEquiv_comp, Equiv.apply_symm_apply] using hh
    rw [lhs_map, rhs_map] at hh'
    exact hh'
  refine ⟨k, t ≫ v, ?_⟩
  rw [F.map_comp]
  refine ⟨build (F.obj k) ss xx yy hss, ?_⟩
  intro r
  rw [cell_build]
  exact (congrArg (fun f : F.obj j ⟶ c.pt ↦ f.app (op ⦋r.degree⦌) (s r))
    (c.w v)).trans (hf r)

end
end DaggerIsoTriangleFilteredStageLift
