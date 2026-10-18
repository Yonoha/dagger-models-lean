import OriginalCounitRightConeQJoinedCofaceReconciled

/-!
# Standard-simplex intersection behind two actual cone cofaces

The two original `joinMap` cofaces are ordinary standard-simplex faces
that omit old vertices. Their image intersection is the face avoiding
both indices. This computes only the large-simplex side; the literal
cone's collapsed base is handled separately by its pushout lemmas.
-/

set_option autoImplicit false

open CategoryTheory Simplicial
open DaggerOriginalCounitRightConeFunctor
open DaggerOriginalCounitRightConeQJoinedCoface

universe u

namespace DaggerOriginalCounitRightConeQJoinedFaceIntersection

noncomputable section

/-- The large-simplex image intersection for two actual cone cofaces is
the standard face omitting both corresponding old vertices. -/
theorem joinMap_coface_range_inter (k : ℕ) (i j : Fin (k + 2)) :
    SSet.Subcomplex.range (joinMap.{u} (SimplexCategory.δ i)) ⊓
      SSet.Subcomplex.range (joinMap.{u} (SimplexCategory.δ j)) =
        SSet.stdSimplex.face.{u}
          ({i.castSucc}ᶜ ⊓ {j.castSucc}ᶜ) := by
  rw [joinMap_delta.{u} k i, joinMap_delta.{u} k j,
    SSet.stdSimplex.range_δ, SSet.stdSimplex.range_δ,
    SSet.stdSimplex.face_inter_face]

end

end DaggerOriginalCounitRightConeQJoinedFaceIntersection
