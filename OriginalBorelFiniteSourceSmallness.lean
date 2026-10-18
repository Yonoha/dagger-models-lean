import OriginalBorelClosedCellFiltration
import OriginalActionFreeCoyoneda

/-!
# Finite free sources preserve the actual countable cell colimits

For a finite simplicial set T, the realization of T is compact. Mathlib's free
Hom adjunction and the retained TopCat closed T₁ embedding colimit theorem then
prove the precise finite-source condition used by the native model package.
-/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MorphismProperty HomotopicalAlgebra Opposite
open scoped TopCat.modelCategory
open DaggerOriginalDaggerRealizationC2Action DaggerOriginalBorelFreeGenerators
open DaggerOriginalBorelClosedCellFiltration DaggerOriginalActionFreeCoyoneda

universe u

namespace DaggerOriginalBorelFiniteSourceSmallness

/-- Every actual finite free realization source preserves the original countable cell colimit. -/
theorem finiteFreeSource_preservesColimit (T : SSet.{u}) [SSet.IsFinite T]
    {X Y : Action TopCat.{u} C2.{u}} (f : X ⟶ Y)
    (hf : RelativeCellComplex.{u} (fun (_ : ℕ) ↦ (I.{u} ⊔ J.{u}).homFamily) f) :
    PreservesColimit hf.F (coyoneda.obj (op (free.obj (SSet.toTop.obj T)))) := by
  have : PreservesColimit (hf.F ⋙ Action.forget TopCat C2)
      (coyoneda.obj (op (SSet.toTop.obj T))) :=
    TopCat.closedT₁Embeddings.preservesColimit_coyoneda_obj_of_compactSpace
      (underlyingClosedCellFiltration f hf) (SSet.toTop.obj T)
  have : PreservesColimit hf.F
      (Action.forget TopCat C2 ⋙ coyoneda.obj (op (SSet.toTop.obj T))) := inferInstance
  exact preservesColimit_of_natIso hf.F
    (freeCoyonedaIso TopCat C2 (SSet.toTop.obj T)).symm

end DaggerOriginalBorelFiniteSourceSmallness
