import Mathlib.AlgebraicTopology.SimplicialSet.FiniteColimits
import TopCatModelCategory.SSet.HasDimensionLT
import TopCatModelCategory.SSet.Coproducts

universe v u

open CategoryTheory Limits

namespace SSet

variable {J : Type u'} [Category.{v'} J] [HasColimitsOfShape J (Type u)]

instance : HasColimitsOfShape J SSet.{u} :=
  inferInstanceAs ( HasColimitsOfShape J (_ ⥤ _))

variable {F : J ⥤ SSet.{u}}

variable (F)

instance hasDimensionLT_colimit (d : ℕ)
    [∀ (j : J), HasDimensionLT (F.obj j) d] : HasDimensionLT (colimit F) d :=
  hasDimensionLT_of_isColimit (n := d) (colimit.isColimit F) inferInstance

end SSet
