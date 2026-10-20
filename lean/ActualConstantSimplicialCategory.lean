import OriginalUnitaryDiscreteEnrichmentRecovered
import DaggerModels.OrdinaryRigidification
import Mathlib.AlgebraicTopology.SimplicialSet.KanComplex
import TopCatModelCategory.ModelCategorySSet

/-! Reuse the existing constant-Hom enrichment for arbitrary ordinary categories. -/

set_option autoImplicit false
open CategoryTheory DaggerModels DaggerUnitaryDiscrete
open scoped SSet.modelCategoryQuillen
universe u

namespace DaggerActualConstantSimplicialCategory
noncomputable section

/-- The original constant-Hom enrichment, bundled without a dagger assumption. -/
abbrev constant (A : Type u) [Category.{u} A] : SimplicialCat.{u, u} :=
  { Obj := A, enriched := ordinaryEnriched A }

/-- Every Hom is the previously defined literal constant simplicial set. -/
theorem constant_hom (A : Type u) [Category.{u} A] (x y : (constant A).Obj) :
    (constant A).enriched.Hom x y = constSSet (x ⟶ y) := rfl

/-- Every constant Hom is Kan, including the empty Hom types. -/
theorem constant_locallyKan (A : Type u) [Category.{u} A] (x y : (constant A).Obj) :
    SSet.KanComplex ((constant A).enriched.Hom x y) :=
  constSSet_fibrant (x ⟶ y)

end
end DaggerActualConstantSimplicialCategory
