import ActualDaggerQuillenEquivalenceReduction
import OriginalGlobalFibrancyRecovered

/-! Fibrant targets are locally Kan; the ordinary counit lemma remains an explicit premise. -/

set_option autoImplicit false
open CategoryTheory HomotopicalAlgebra DaggerModels
open DaggerModels.OrdinaryRigidification
open DaggerActualRigidificationQuillen DaggerActualQuillenEquivalenceReduction
universe u

namespace DaggerActualFibrantCounitReduction

noncomputable section
local instance : ModelCategory D.{u} := modelD.{u}
local instance : ModelCategory G.{u} := modelG.{u}

/-- Fibrancy in the constructed actual target model is precisely local Kan fibrancy. -/
theorem fibrant_iff_localKan (C : G.{u}) :
    IsFibrant C ↔ ∀ x y : C.Obj, SSet.KanComplex (C.enriched.Hom x y) :=
  DaggerGlobalFibrancy.standard_fibrant_iff_original C

/-- This ordinary local-counit statement is an outstanding theorem, not a new axiom. -/
abbrev OrdinaryCounitLocalGW : Prop :=
  ∀ C : SimplicialCat.{u, u},
    (∀ x y : C.Obj, SSet.KanComplex (C.enriched.Hom x y)) →
      ∀ a b : (rigidification.obj (coherentNerve.obj C)).Obj,
        DaggerSSetGluing.GW ((rigidificationCoherentNerveAdjunction.counit.app C).map a b)

/-- An ordinary local-counit proof gives weakness of the same actual fibrant dagger counit. -/
theorem fibrant_counit_weak_of_ordinary_local (hlocal : OrdinaryCounitLocalGW.{u})
    (C : G.{u}) (hC : IsFibrant C) : WeakEquivalence (adjunction.counit.app C) := by
  apply counit_weak_of_local
  intro a b
  change DaggerSSetGluing.GW
    ((DaggerAdjunction.daggerRigidificationCoherentNerveAdjunction.counit.app C).map a b)
  rw [DaggerAdjunction.adjunction_counit C]
  exact hlocal C.toSimplicialCat ((fibrant_iff_localKan C).1 hC) a b

/-- The actual Quillen equivalence follows once this precise ordinary theorem is proved. -/
theorem isQuillenEquivalence_of_ordinary_local (hlocal : OrdinaryCounitLocalGW.{u}) :
    adjunction.{u}.IsQuillenEquivalence := by
  apply isQuillenEquivalence_of_counit
  exact fibrant_counit_weak_of_ordinary_local hlocal

end
end DaggerActualFibrantCounitReduction
