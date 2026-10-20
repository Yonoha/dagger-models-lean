import OriginalFixedObjectMappingPathData
import Mathlib.CategoryTheory.Limits.Constructions.Equalizers

/-!
# Native finite limits in both original fixed-object strict groupoid categories

Reuse Mathlib's terminal-and-pullbacks construction with the actual terminal
and full pullbacks proved on the original objects and full enriched functors.
-/

set_option autoImplicit false
open CategoryTheory Limits
open DaggerOriginalFixedObjectSimplicialCategories DaggerOriginalFixedObjectDaggerCategories
universe u
namespace DaggerOriginalFixedObjectFiniteLimits
noncomputable section

/-- The full original ordinary pullbacks supply the native class for every cospan. -/
instance strictHasPullbacks (O : Type u) : HasPullbacks (FixedStrictGroupoids O) :=
  hasPullbacks_of_hasLimit_cospan _

/-- The unchanged original ordinary strict category has native finite limits. -/
instance strictHasFiniteLimits (O : Type u) : HasFiniteLimits (FixedStrictGroupoids O) :=
  hasFiniteLimits_of_hasTerminal_and_pullbacks

/-- The full original dagger pullbacks supply the native class for every cospan. -/
instance strictDaggerHasPullbacks (O : Type u) : HasPullbacks (FixedStrictDaggerGroupoids O) :=
  hasPullbacks_of_hasLimit_cospan _

/-- The unchanged original strict dagger category has native finite limits. -/
instance strictDaggerHasFiniteLimits (O : Type u) :
    HasFiniteLimits (FixedStrictDaggerGroupoids O) :=
  hasFiniteLimits_of_hasTerminal_and_pullbacks

end
end DaggerOriginalFixedObjectFiniteLimits
