import DaggerModels.Presheaf
import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
import Mathlib.CategoryTheory.Limits.Types.Colimits
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory

/-!
# The free dagger simplicial-set adjunction

This constructs the free--forgetful adjunction on simplicial sets in Part I,
`dj.not.adjunctions`. The free functor is a chosen left Kan extension along the inclusion
of the ordinary simplex category in the reversal simplex category, transported through
`daggerSSetEquivalencePresheaf`.

The identification with the explicit pushout $A \amalg_{\operatorname{sk}_0 A} A^{\mathrm{op}}$
is not proved here.
-/

open CategoryTheory Functor

universe u

namespace DaggerModels

/-- Restriction of reversal presheaves along the ordinary simplex inclusion. -/
abbrev presheafRestriction : (ReverseSimplexᵒᵖ ⥤ Type u) ⥤ SSet.{u} :=
  (whiskeringLeft _ _ (Type u)).obj ReverseSimplex.inclusion.op

/-- Pointwise left Kan extensions exist because the indexing comma categories are small
and `Type u` has all small colimits. -/
local instance (A : SSet.{u}) : ReverseSimplex.inclusion.op.HasPointwiseLeftKanExtension A :=
  fun _ ↦ inferInstance

/-- The free dagger functor obtained by left Kan extension and the presheaf equivalence. -/
noncomputable def freeDagger : SSet.{u} ⥤ DaggerSSet.{u} :=
  ReverseSimplex.inclusion.op.lan ⋙ ReversePresheaf.toDaggerSSet

/-- Forgetting a restricted presheaf is ordinary presheaf restriction. -/
def restrictionForgetIso :
    ReversePresheaf.toDaggerSSet ⋙ DaggerSSet.forget.{u} ≅ presheafRestriction :=
  Iso.refl _

/-- Extending a dagger simplicial set and then restricting recovers its underlying set. -/
noncomputable def extensionRestrictionIso :
    DaggerSSet.toPresheaf ⋙ presheafRestriction ≅ DaggerSSet.forget.{u} :=
  isoWhiskerLeft DaggerSSet.toPresheaf restrictionForgetIso.symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    isoWhiskerRight DaggerSSet.unitIso.symm DaggerSSet.forget ≪≫
    Functor.leftUnitor DaggerSSet.forget

/-- The actual adjunction to the original dagger-simplicial-set forgetful functor. -/
noncomputable def freeDaggerAdjunction : freeDagger.{u} ⊣ DaggerSSet.forget.{u} :=
  ((ReverseSimplex.inclusion.op.lanAdjunction (Type u)).comp
    daggerSSetEquivalencePresheaf.symm.toAdjunction).ofNatIsoRight extensionRestrictionIso

/-- There exists a free dagger functor left adjoint to forgetting the dagger. -/
theorem exists_freeDaggerAdjunction :
    ∃ F : SSet.{u} ⥤ DaggerSSet.{u}, Nonempty (F ⊣ DaggerSSet.forget.{u}) :=
  ⟨freeDagger, ⟨freeDaggerAdjunction⟩⟩

namespace DaggerSSet

/-- The forgetful functor preserves all `u`-small limits as a right adjoint. -/
theorem forget_preservesLimits : Limits.PreservesLimits forget.{u} :=
  Adjunction.rightAdjoint_preservesLimits freeDaggerAdjunction

/-- Forgetting the dagger preserves `u`-small colimits, since restriction of
presheaves computes them pointwise. -/
theorem forget_preservesColimits : Limits.PreservesColimits forget.{u} := by
  let : Limits.PreservesColimits toPresheaf.{u} :=
    Adjunction.leftAdjoint_preservesColimits daggerSSetEquivalencePresheaf.toAdjunction
  let : Limits.PreservesColimits presheafRestriction.{u} :=
    whiskeringLeft_preservesColimit ReverseSimplex.inclusion.op
  exact Limits.preservesColimits_of_natIso extensionRestrictionIso

end DaggerSSet

end DaggerModels
