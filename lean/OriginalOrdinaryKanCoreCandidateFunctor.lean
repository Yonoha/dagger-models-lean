import OriginalOrdinaryKanCoreFunctor

/-!
# The ordinary core candidate as an endofunctor

This packages the literal range/preimage candidate and its inclusion in
the identity functor. It makes no Kan, maximality, or dagger claim.
-/

set_option autoImplicit false

open CategoryTheory

universe u

namespace DaggerOriginalOrdinaryKanCoreSubcomplex

noncomputable section

/-- The candidate preimage construction is functorial on arbitrary
simplicial sets, before any quasi-category hypothesis. -/
def ordinaryCoreCandidateFunctor : SSet.{u} ⥤ SSet.{u} where
  obj X := (ordinaryCoreCandidate X : SSet.{u})
  map f := ordinaryCoreCandidateMap f
  map_id X := by
    ext n s
    apply Subtype.ext
    rfl
  map_comp f g := by
    ext n s
    apply Subtype.ext
    rfl

/-- The actual subcomplex inclusions form a natural transformation. -/
def ordinaryCoreCandidateInclusion :
    ordinaryCoreCandidateFunctor.{u} ⟶ 𝟭 SSet.{u} where
  app X := (ordinaryCoreCandidate X).ι
  naturality _ _ f := ordinaryCoreCandidateMap_comp_ι f

end

end DaggerOriginalOrdinaryKanCoreSubcomplex
