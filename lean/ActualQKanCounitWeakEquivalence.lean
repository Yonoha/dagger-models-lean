import NativeAllCofibrantLocalizationReflection
import ActualQOriginalCounitLocalization

/-! The unchanged original-Q adjunction counit is geometrically weak on every Kan complex. -/

set_option autoImplicit false
open CategoryTheory HomotopicalAlgebra
open DaggerOriginalCounitRightConeQRealizationAdjunction DaggerSSetGluing
open DaggerNativeAllCofibrantLocalizationReflection
open scoped SSet.modelCategoryQuillen
universe u

namespace DaggerActualQKanCounitWeakEquivalence
noncomputable section

/-- All original simplicial sets are native cofibrant objects; no source Kan premise is added. -/
theorem weakEquivalence_of_localization_isIso {X Y : SSet.{u}} (f : X ⟶ Y)
    [Y.KanComplex] [IsIso ((weakEquivalences SSet.{u}).Q.map f)] : WeakEquivalence f := by
  have : ∀ X : SSet.{u}, IsCofibrant X := fun X ↦ inferInstance
  exact DaggerNativeAllCofibrantLocalizationReflection.weakEquivalence_of_localization_isIso
    (weakEquivalences SSet.{u}).Q f

/-- Native localization reflection applies to precisely the already proved original counit. -/
theorem counit_weakEquivalence (X : SSet.{u}) [X.KanComplex] :
    WeakEquivalence (realizationSingularAdjunction.counit.app X) := by
  have := DaggerActualQOriginalCounitLocalization.counit_localized_isIso
    (weakEquivalences SSet.{u}).Q X
  exact weakEquivalence_of_localization_isIso (realizationSingularAdjunction.counit.app X)

/-- The literal original-Q counit is geometrically weak for every original Kan target. -/
theorem counit_GW (X : SSet.{u}) [X.KanComplex] :
    GW (realizationSingularAdjunction.counit.app X) :=
  (weakEquivalence_iff_GW _).mp (counit_weakEquivalence X)

end
end DaggerActualQKanCounitWeakEquivalence
