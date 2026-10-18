import OriginalZeroBoundaryShapeIso
import OriginalCosliceLeftLiftingProperty

/-!
# The exact zero-prefix boundary projection is an isomorphism

The original projection evaluates on the actual suffix inclusion. That
inclusion is already proved to be the forward map of the native natural
shape isomorphism. Yoneda therefore makes the projection bijective in every
degree, and the native componentwise criterion proves this same projection
is an isomorphism. No quasi-category or filling hypothesis is required.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial
open DaggerOriginalJoinedBoundaryRestriction
open DaggerOriginalJoinedBoundarySuffixInclusion
open DaggerOriginalJoinedBoundaryProjection
open DaggerOriginalZeroBoundaryShapeIso

universe u

namespace DaggerOriginalZeroBoundaryProjectionIso

noncomputable section

/-- The original zero-prefix projection is bijective in every actual presheaf degree. -/
theorem boundaryProjection_zero_app_bijective (X : SSet.{u}) (n : SimplexCategoryᵒᵖ) :
    Function.Bijective ((boundaryProjection 0 X).app n) := by
  let θ := boundarySuffixInclusion.{u} 0 n.unop
  haveI : IsIso θ := boundarySuffixInclusion_zero_isIso n.unop
  let e := asIso θ
  constructor
  · intro g h heq
    apply (cancel_epi θ).mp
    exact SSet.yonedaEquiv.injective heq
  · intro s
    refine ⟨e.inv ≫ (SSet.yonedaEquiv (X := X) (n := n.unop)).symm s, ?_⟩
    change SSet.yonedaEquiv (e.hom ≫
      (e.inv ≫ (SSet.yonedaEquiv (X := X) (n := n.unop)).symm s)) = s
    rw [e.hom_inv_id_assoc, Equiv.apply_symm_apply]

/-- The same original boundary projection is a native isomorphism of simplicial sets. -/
theorem boundaryProjection_zero_isIso (X : SSet.{u}) : IsIso (boundaryProjection 0 X) :=
  (NatTrans.isIso_iff_isIso_app _).mpr (fun n ↦
    (isIso_iff_bijective _).mpr (boundaryProjection_zero_app_bijective X n))

/-- The original zero-prefix boundary-map presheaf is isomorphic to the original X. -/
def zeroBoundaryProjectionIso (X : SSet.{u}) : boundaryJoinedPresheaf 0 X ≅ X := by
  haveI := boundaryProjection_zero_isIso X
  exact asIso (boundaryProjection 0 X)

/-- The forward map of this isomorphism is exactly the original boundary projection. -/
theorem zeroBoundaryProjectionIso_hom (X : SSet.{u}) :
    (zeroBoundaryProjectionIso X).hom = boundaryProjection 0 X := rfl

/-- Its original inverse followed by the original projection is the original identity. -/
theorem zeroBoundaryProjectionIso_inv_comp (X : SSet.{u}) :
    (zeroBoundaryProjectionIso X).inv ≫ boundaryProjection 0 X = 𝟙 _ :=
  (zeroBoundaryProjectionIso X).inv_hom_id

/-- The original zero-prefix projection has the native lifting property for every morphism. -/
theorem boundaryProjection_zero_hasLiftingProperty (X : SSet.{u})
    {A B : SSet.{u}} (i : A ⟶ B) : HasLiftingProperty i (boundaryProjection 0 X) := by
  haveI := boundaryProjection_zero_isIso X
  infer_instance

end

end DaggerOriginalZeroBoundaryProjectionIso
