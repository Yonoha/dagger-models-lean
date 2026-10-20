import OriginalSimplicialCategoryGroupoidHomTransport

/-!
# A raw simplicial homotopy equivalence is a native weak equivalence

No fibrancy of the original simplicial sets is required. Realization and
singular carry the supplied homotopies to the native Kan complexes, where
TopCatModelCategory's existing homotopy-equivalence criterion applies.
-/
set_option autoImplicit false
open CategoryTheory HomotopicalAlgebra
universe u
namespace DaggerNativeSSetRawHomotopyEquivalenceWeak
noncomputable section

/-- Realize and singularize both supplied raw homotopies, preserving the exact maps. -/
def realizedSingularHomotopyEquiv {X Y : SSet.{u}} (e : SSet.HomotopyEquiv X Y) :
    SSet.HomotopyEquiv (DaggerNerveHomotopy.R.obj X) (DaggerNerveHomotopy.R.obj Y) where
  hom := DaggerNerveHomotopy.R.map e.hom
  inv := DaggerNerveHomotopy.R.map e.inv
  homInvId := (e.homInvId.toTop.toSSet).congr
    (DaggerNerveHomotopy.R.map_comp e.hom e.inv)
    (DaggerNerveHomotopy.R.map_id X)
  invHomId := (e.invHomId.toTop.toSSet).congr
    (DaggerNerveHomotopy.R.map_comp e.inv e.hom)
    (DaggerNerveHomotopy.R.map_id Y)

/-- The exact original hom map is weak, without Kan hypotheses on either original object. -/
theorem rawHomotopyEquiv_weakEquivalence {X Y : SSet.{u}} (e : SSet.HomotopyEquiv X Y) :
    WeakEquivalence e.hom := by
  apply (SSet.modelCategoryQuillen.weakEquivalence_iff _).mpr
  apply (TopCat.modelCategory.weakEquivalence_iff _).mpr
  exact SSet.KanComplex.W.homotopyEquivHom (realizedSingularHomotopyEquiv e)

end
end DaggerNativeSSetRawHomotopyEquivalenceWeak
