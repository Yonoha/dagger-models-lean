import OriginalFixedObjectDaggerColimits
import OriginalCommutativeActionColimits

/-!
# Colimits of the original fixed-object ordinary strict groupoids

The actual dagger-action equivalence transfers the already constructed dagger colimits.
The colimit of trivial C2 actions has trivial action, so its underlying original groupoid
has the full ordinary colimit universal property. No ordinary model structure is assumed.
-/

set_option autoImplicit false
open CategoryTheory Limits
open DaggerOriginalDaggerRealizationC2Action
open DaggerOriginalFixedObjectSimplicialCategories
open DaggerOriginalFixedObjectDaggerActionEquivalence
universe u
namespace DaggerOriginalFixedObjectGroupoidColimits
noncomputable section

/-- Transport the actual strict dagger colimits to the equivalent full native C2 action category. -/
instance fixedActionHasColimits (O : Type u) :
    HasColimitsOfSize.{u, u} (Action (FixedStrictGroupoids O) C2.{u}) :=
  Adjunction.has_colimits_of_equivalence (fixedDaggerActionEquivalence O).inverse

/-- Recover every original ordinary strict groupoid colimit from trivial C2 actions. -/
instance strictHasColimits (O : Type u) : HasColimitsOfSize.{u, u} (FixedStrictGroupoids O) :=
  DaggerOriginalCommutativeActionColimits.hasColimits_of_action (M := C2.{u})

/-- The original ordinary strict groupoids consequently have native finite colimits. -/
instance strictHasFiniteColimits (O : Type u) : HasFiniteColimits (FixedStrictGroupoids O) :=
  hasFiniteColimits_of_hasColimitsOfSize.{u, u} _

end
end DaggerOriginalFixedObjectGroupoidColimits
