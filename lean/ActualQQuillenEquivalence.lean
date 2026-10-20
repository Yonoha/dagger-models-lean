import ActualQKanCounitWeakEquivalence
import ActualQRealizationWeakReflection
import ActualQRealizationQuillen

/-! The original Q realization-singular adjunction is a native Kan Quillen equivalence. -/

set_option autoImplicit false
open CategoryTheory HomotopicalAlgebra
open DaggerOriginalCounitRightConeQRealizationAdjunction
open scoped SSet.modelCategoryQuillen
universe u

namespace DaggerActualQQuillenEquivalence
noncomputable section

/-- The literal original adjunction satisfies the native Quillen equivalence criterion. -/
theorem isQuillenEquivalence : realizationSingularAdjunction.{u}.IsQuillenEquivalence := by
  refine
    { toIsQuillenAdjunction := DaggerActualQRealizationQuillen.isQuillen
      weakEquivalence_homEquiv_iff := ?_ }
  intro X Y _ _ f
  have : WeakEquivalence (realizationSingularAdjunction.counit.app Y) :=
    DaggerActualQKanCounitWeakEquivalence.counit_weakEquivalence Y
  let g : X ⟶ singular.obj Y := realizationSingularAdjunction.homEquiv X Y f
  have htriangle : realization.map g ≫ realizationSingularAdjunction.counit.app Y = f := by
    calc
      realization.map g ≫ realizationSingularAdjunction.counit.app Y =
          (realizationSingularAdjunction.homEquiv X Y).symm g :=
        (realizationSingularAdjunction.homEquiv_counit X Y g).symm
      _ = f := Equiv.symm_apply_apply _ _
  calc
    WeakEquivalence g ↔ WeakEquivalence (realization.map g) :=
      (DaggerActualQRealizationWeakReflection.realization_weakEquivalence_iff g).symm
    _ ↔ WeakEquivalence (realization.map g ≫ realizationSingularAdjunction.counit.app Y) :=
      (weakEquivalence_postcomp_iff _ _).symm
    _ ↔ WeakEquivalence f := by rw [htriangle]

end
end DaggerActualQQuillenEquivalence
