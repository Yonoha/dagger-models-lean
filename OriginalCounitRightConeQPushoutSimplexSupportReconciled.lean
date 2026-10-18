import OriginalCounitRightConeFunctor
import Mathlib.CategoryTheory.Limits.Types.Pushouts
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic

/-!
# Pointwise support of the literal collapsed-face right cone

The right cone is still the original pushout, rather than a simplex or a
cube. At every simplicial degree a point is either on its collapsed base
or comes from a large-simplex operator not in the attaching-face image.
This is the first pointwise input for calculating intersections of the
actual cone coface images.
-/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite Simplicial
open DaggerOriginalCounitRightCone

universe u

namespace DaggerOriginalCounitRightConeQPushoutSimplexSupport

noncomputable section

/-- Evaluation of the original simplicial pushout is the corresponding
pushout of types in every degree. -/
theorem cone_pointwise_isPushout (n : ℕ) (q : SimplexCategoryᵒᵖ) :
    IsPushout ((face.{u} n).app q) ((collapse.{u} n).app q)
      ((simplexIncl.{u} n).app q) ((baseIncl.{u} n).app q) := by
  let ev : SSet.{u} ⥤ Type u := (evaluation SimplexCategoryᵒᵖ (Type u)).obj q
  have h := isColimitOfPreserves ev (pushoutIsPushout (face.{u} n) (collapse.{u} n))
  exact IsPushout.of_isColimit
    (isColimitMapCoconePushoutCoconeEquiv ev (face_eq_collapse.{u} n) h)

/-- Literal base-or-tip decomposition of each right-cone simplex. The
second case keeps the original large-simplex operator outside the face
that is collapsed in the pushout. -/
theorem cone_simplex_base_or_tip (n : ℕ) (q : SimplexCategoryᵒᵖ)
    (x : (cone.{u} n).obj q) :
    (∃ y : (Δ[0] : SSet.{u}).obj q,
      (baseIncl.{u} n).app q y = x) ∨
    (∃ y : (Δ[n + 1] : SSet.{u}).obj q,
      (simplexIncl.{u} n).app q y = x ∧
        y ∉ Set.range ((face.{u} n).app q)) := by
  exact CategoryTheory.Limits.Types.eq_or_eq_of_isPushout'
    (cone_pointwise_isPushout.{u} n q).flip x

end

end DaggerOriginalCounitRightConeQPushoutSimplexSupport
