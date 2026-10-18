import OriginalTaggedReversePresheafInclusion
import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction

/-!
# Both Kan-extension adjunctions for the actual tagged quotient

The central functor in both transported adjunctions is the existing
`presheafRoute`, which restricts along the actual `qTag.op`.
-/

set_option autoImplicit false

open CategoryTheory

universe u

namespace DaggerModels.OriginalTaggedReverseAdjunctions

open DaggerModels.OriginalTaggedReverseSimplex
open TaggedReverseSimplex
open DaggerModels.OriginalTaggedReversePrecomposition
open DaggerModels.OriginalTaggedReversePresheafInclusion

private instance (F : TaggedReverseSimplexᵒᵖ ⥤ Type u) :
    (qTag.op).HasPointwiseLeftKanExtension F := fun _ => inferInstance

private instance (F : TaggedReverseSimplexᵒᵖ ⥤ Type u) :
    (qTag.op).HasPointwiseRightKanExtension F := fun _ => inferInstance

/-- The presheaf-level left Kan extension of the actual tagged quotient. -/
noncomputable def presheafLeftAdjunction :
    (qTag.op).lan ⊣ precomposition (Type u) :=
  qTag.op.lanAdjunction (Type u)

/-- The presheaf-level right Kan extension of the same restriction. -/
noncomputable def presheafRightAdjunction :
    precomposition (Type u) ⊣ (qTag.op).ran :=
  qTag.op.ranAdjunction (Type u)

/-- Left adjoint of the existing actual dagger-to-anti-involutive route. -/
noncomputable def leftKan : AntiInvolutiveSSet.{u} ⥤ DaggerSSet.{u} :=
  (antiInvolutiveEquivalence.{u}.functor ⋙ (qTag.op).lan) ⋙
    daggerSSetEquivalencePresheaf.{u}.inverse

/-- Right adjoint of the same existing route. -/
noncomputable def rightKan : AntiInvolutiveSSet.{u} ⥤ DaggerSSet.{u} :=
  (antiInvolutiveEquivalence.{u}.functor ⋙ (qTag.op).ran) ⋙
    daggerSSetEquivalencePresheaf.{u}.inverse

/-- The actual left Kan extension is left adjoint to `presheafRoute`. -/
noncomputable def leftAdjunction : leftKan.{u} ⊣ presheafRoute.{u} :=
  (antiInvolutiveEquivalence.{u}.toAdjunction.comp
    presheafLeftAdjunction.{u}).comp
      daggerSSetEquivalencePresheaf.{u}.symm.toAdjunction

/-- The same `presheafRoute` is left adjoint to the right Kan extension. -/
noncomputable def rightAdjunction : presheafRoute.{u} ⊣ rightKan.{u} :=
  daggerSSetEquivalencePresheaf.{u}.toAdjunction.comp
    (presheafRightAdjunction.{u}.comp
      antiInvolutiveEquivalence.{u}.symm.toAdjunction)

end DaggerModels.OriginalTaggedReverseAdjunctions
