import OriginalFixedObjectDaggerFilteredColimits
import Mathlib.CategoryTheory.Presentable.Adjunction

/-! The actual original strict inclusion preserves filtered colimits and is aleph0 accessible. -/
set_option autoImplicit false
open CategoryTheory Limits
open DaggerOriginalFixedObjectGroupoidCompletionAdjunction
open DaggerOriginalFixedObjectDaggerFilteredColimits
open DaggerOriginalFixedObjectStrictDaggerGenerators
universe u
namespace DaggerOriginalFixedObjectDaggerAccessibleInclusion
noncomputable section
attribute [local instance] Cardinal.fact_isRegular_aleph0

/-- The original inclusion preserves the full colimit of every filtered diagram. -/
instance inclusionPreservesFiltered (O J : Type u) [SmallCategory J] [IsFiltered J] :
    PreservesColimitsOfShape J (fixedDaggerInclusion O) where
  preservesColimit {K} :=
    preservesColimit_of_preserves_colimit_cocone (filteredIsColimit K) (mappedFilteredIsColimit K)

/-- Preservation of filtered colimits gives actual aleph0 accessibility of the inclusion. -/
instance inclusionAccessible (O : Type u) :
    (fixedDaggerInclusion O).IsCardinalAccessible Cardinal.aleph0.{u} where
  preservesColimitOfShape J _categoryJ filteredJ := by
    letI : IsFiltered J := (isCardinalFiltered_aleph0_iff J).mp filteredJ
    infer_instance

/-- The exact legacy presentation preserves this accessibility under equivalence. -/
instance legacyInclusionAccessible (O : Type u) :
    (strictLegacyInclusion O).IsCardinalAccessible Cardinal.aleph0.{u} := by
  unfold strictLegacyInclusion
  infer_instance

end
end DaggerOriginalFixedObjectDaggerAccessibleInclusion
