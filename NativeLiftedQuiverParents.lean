import NativeLiftedQuiverSignedTriangles
import NativeFreeGroupoidDescendingEdges

/-! Every actual non-root lifted vertex has exactly one descending signed edge. -/
set_option autoImplicit false
open CategoryTheory
open DaggerNativeFreePathCompletionQuiverBridge DaggerNativePathUnitLiftedQuiver
open DaggerNativeLiftedQuiverHeight DaggerNativeLiftedQuiverSignedTriangles
open DaggerNativeFreeGroupoidWordLabels DaggerNativeFreeGroupoidNormalPath
open DaggerNativeFreeGroupoidDescendingEdges
universe u
namespace DaggerNativeLiftedQuiverParents
noncomputable section

variable (V : Type u) [Quiver.{u + 1} V] (a : V)

theorem existsUnique_parent (x : Vertex V ((pathUnit V).obj (show Paths V from a)))
    (hx : x ≠ root V a) :
    ∃! s : Quiver.Star (show Quiver.Symmetrify (Vertex V ((pathUnit V).obj a)) from x),
      height V a s.1 + 1 = height V a x := by
  let P := (projection V ((pathUnit V).obj (show Paths V from a))).symmetrify
  have hP : P.IsCovering := signed_projection_isCovering V _
  have hpos : norm V (a := (show Quiver.Symmetrify V from a))
      (b := (show Quiver.Symmetrify V from x.right)) x.hom ≠ 0 := by
    intro h
    exact hx ((height_zero_iff V a x).mp h)
  obtain ⟨s, hs, hu⟩ := existsUnique_descending_edge V x.hom hpos
  obtain ⟨t, ht⟩ := (hP.star_bijective x).2 s
  refine ⟨t, ?_, ?_⟩
  · rw [← ht] at hs
    change norm V (x.hom ≫ (quotientMap V).map (P.map t.2).toPath) + 1 = _ at hs
    rw [signed_triangle V _ t.2] at hs
    exact hs
  · intro z hz
    apply (hP.star_bijective x).1
    rw [ht]
    apply hu
    change norm V (x.hom ≫ (quotientMap V).map (P.map z.2).toPath) + 1 = _
    rw [signed_triangle V _ z.2]
    exact hz

end
end DaggerNativeLiftedQuiverParents
