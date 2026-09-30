import DaggerModels.DaggerGraphPresheafUnit
import DaggerModels.DaggerGraphPresheafCounit

/-!
# Dagger simplicial graphs are presheaves

The actual total-edge and endpoint-fiber functors are inverse equivalences.
Their natural unit/counit retain all vertices and edge simplices. This supplies
the graph presentability ingredient in Part I `bg.lem.presentable`.
-/

open CategoryTheory Opposite

universe u

namespace DaggerModels

/-- The full graph category is equivalent to presheaves on the concrete small index. -/
noncomputable def daggerGraphEquivalencePresheaf :
    DaggerSimplicialGraph.{u} ≌ (DaggerGraphIndex.Objᵒᵖ ⥤ Type u) where
  functor := DaggerGraphPresheaf.functor
  inverse := DaggerGraphPresheaf.inverse
  unitIso := DaggerGraphPresheaf.unitIso
  counitIso := DaggerGraphPresheaf.counitIso
  functor_unitIso_comp G := by
    ext X e
    cases X using Opposite.rec
    rename_i X
    cases X with
    | vertex => rfl
    | edge n =>
      rcases e with ⟨x, y, e⟩
      rfl

/-- A literal small-index presheaf equivalence, with the indexing witness supplied. -/
theorem exists_daggerGraphPresheafEquivalence :
    ∃ (I : Type) (hI : SmallCategory I),
      letI := hI
      Nonempty (DaggerSimplicialGraph.{u} ≌ (Iᵒᵖ ⥤ Type u)) :=
  ⟨DaggerGraphIndex.Obj, inferInstance, ⟨daggerGraphEquivalencePresheaf⟩⟩

end DaggerModels
