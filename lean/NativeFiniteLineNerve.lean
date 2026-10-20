import NativeFiniteLinePaths

/-! An exact native simplex isomorphism retaining every original finite-line vertex. -/
set_option autoImplicit false
open CategoryTheory Simplicial Opposite
open DaggerNativeFiniteLinePaths
universe u
namespace DaggerNativeFiniteLineNerve
noncomputable section

def ordinalIso (n : ℕ) : nerve (Paths (Vertex.{u} n)) ≅ nerve (ULift.{u} (Fin (n + 1))) where
  hom := nerveMap (toOrdinal.{u} n)
  inv := nerveMap (fromOrdinal.{u} n)
  hom_inv_id := by
    change nerveFunctor.{u,u}.map (toOrdinal.{u} n).toCatHom ≫
      nerveFunctor.{u,u}.map (fromOrdinal.{u} n).toCatHom = _
    rw [← nerveFunctor.{u,u}.map_comp]
    change nerveFunctor.{u,u}.map (toOrdinal.{u} n ⋙ fromOrdinal.{u} n).toCatHom = _
    rw [to_from]
    exact nerveFunctor.{u,u}.map_id _
  inv_hom_id := by
    change nerveFunctor.{u,u}.map (fromOrdinal.{u} n).toCatHom ≫
      nerveFunctor.{u,u}.map (toOrdinal.{u} n).toCatHom = _
    rw [← nerveFunctor.{u,u}.map_comp]
    change nerveFunctor.{u,u}.map (fromOrdinal.{u} n ⋙ toOrdinal.{u} n).toCatHom = _
    rw [from_to]
    exact nerveFunctor.{u,u}.map_id _

def simplexIso (n : ℕ) : nerve (Paths (Vertex.{u} n)) ≅ (Δ[n] : SSet.{u}) :=
  ordinalIso n ≪≫ (SSet.stdSimplex.isoNerve n).symm

theorem simplexIso_hom_value {n d : ℕ} (c : ComposableArrows (Paths (Vertex.{u} n)) d)
    (i : Fin (d + 1)) :
    SSet.stdSimplex.asOrderHom ((simplexIso n).hom.app (op ⦋d⦌) c) i = (c.obj i).index := by
  change SSet.stdSimplex.asOrderHom
    ((SSet.stdSimplex.isoNerve n).inv.app (op ⦋d⦌)
      ((nerveMap.{u,u} (toOrdinal.{u} n)).app _ c)) i = _
  exact SSet.stdSimplex.isoNerve_inv_app_apply
    ((nerveMap.{u,u} (toOrdinal.{u} n)).app (op ⦋d⦌) c) i

theorem simplexIso_inv_value {n d : ℕ} (c : (Δ[n] : SSet.{u}).obj (op ⦋d⦌))
    (i : Fin (d + 1)) :
    (((simplexIso n).inv.app (op ⦋d⦌) c).obj i).index = SSet.stdSimplex.asOrderHom c i := by
  change (((SSet.stdSimplex.isoNerve n).hom.app (op ⦋d⦌) c).obj i).down = _
  rw [SSet.stdSimplex.isoNerve_hom_app_apply]
  rfl

end
end DaggerNativeFiniteLineNerve
