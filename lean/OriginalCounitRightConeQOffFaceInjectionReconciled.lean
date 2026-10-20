import OriginalCounitRightConeQBaseTipCollisionReconciled

/-!
# Injection of the literal cone's large-simplex leg off its collapsed face

The original `simplexIncl` identifies attaching-face operators, so it is
not globally injective. The pushout equivalence relation is trivial if
one of two large-simplex operators is outside that face. This is the
precise form needed to identify intersections of cone coface images.
-/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite Simplicial
open DaggerOriginalCounitRightCone
open DaggerOriginalCounitRightConeQPushoutSimplexSupport
open DaggerOriginalCounitRightConeQBaseTipCollision

universe u

namespace DaggerOriginalCounitRightConeQOffFaceInjection

noncomputable section

/-- The canonical Type pushout does not identify a point outside the
attaching-image with any other point of the large-simplex side. -/
theorem canonical_inl_injective_off_face
    {S A B : Type u} (f : S ⟶ A) (g : S ⟶ B)
    (hf : Function.Injective f) (x y : A)
    (hx : x ∉ Set.range f)
    (h : CategoryTheory.Limits.Types.Pushout.inl f g x =
      CategoryTheory.Limits.Types.Pushout.inl f g y) : x = y := by
  letI : Mono f := (CategoryTheory.mono_iff_injective f).2 hf
  have hr :=
    (CategoryTheory.Limits.Types.Pushout.quot_mk_eq_iff f g
      (Sum.inl x) (Sum.inl y)).1 h
  rcases (CategoryTheory.Limits.Types.Pushout.inl_rel'_inl_iff
    f g x y).1 hr with hxy | ⟨s, t, _, hs, _⟩
  · exact hxy
  · exact False.elim (hx ⟨s, hs.symm⟩)

/-- Off the attaching face, the large-simplex map into the actual right
cone is injective on every simplicial degree. -/
theorem simplexIncl_injective_off_face (n : ℕ) (q : SimplexCategoryᵒᵖ)
    (x y : (Δ[n + 1] : SSet.{u}).obj q)
    (hx : x ∉ Set.range ((face.{u} n).app q))
    (hxy : (simplexIncl.{u} n).app q x =
      (simplexIncl.{u} n).app q y) : x = y := by
  let f := (face.{u} n).app q
  let g := (collapse.{u} n).app q
  have hf : Function.Injective f := by
    exact stdSimplex_map_app_injective.{u}
      (SimplexCategory.δ (Fin.last (n + 1))) q
  let e := Cocones.ext
    (IsColimit.coconePointUniqueUpToIso
      (CategoryTheory.Limits.Types.Pushout.isColimitCocone f g)
      (cone_pointwise_isPushout.{u} n q).isColimit) (by simp)
  have hcan : CategoryTheory.Limits.Types.Pushout.inl f g x =
      CategoryTheory.Limits.Types.Pushout.inl f g y := by
    apply (CategoryTheory.mono_iff_injective e.hom.hom).1 inferInstance
    have hx' := congrFun (e.hom.w WalkingSpan.left) x
    have hy' := congrFun (e.hom.w WalkingSpan.left) y
    exact hx'.trans (hxy.trans hy'.symm)
  exact canonical_inl_injective_off_face f g hf x y hx hcan

end

end DaggerOriginalCounitRightConeQOffFaceInjection
