import OriginalExtremeHorn
import Mathlib.AlgebraicTopology.SimplicialSet.KanComplex

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

universe u

namespace DaggerOrdinaryRigidificationCof.PathFacets

variable {n : ℕ} (k : interior n)

/-- Every map from the literal extreme horn into a Kan complex extends. -/
theorem extremeHorn_extension {X : SSet.{u}} [SSet.KanComplex X]
    (a : (extremeHorn n k).toSSet ⟶ X) :
    ∃ b : extremeHom n ⟶ X, (extremeHorn n k).ι ≫ b = a := by
  letI := extremeHorn_lifting n k (terminal.from X) inferInstance
  have sq : CommSq a (extremeHorn n k).ι (terminal.from X)
      (terminal.from (extremeHom n)) := ⟨by simp⟩
  exact ⟨sq.lift, sq.fac_left⟩

end DaggerOrdinaryRigidificationCof.PathFacets
