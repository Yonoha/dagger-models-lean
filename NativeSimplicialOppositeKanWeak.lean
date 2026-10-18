import OriginalHornFillingReversal
import TopCatModelCategory.QuillenAdjunction
import ActualQRealizationWeakEquivalences

/-! Native simplicial reversal preserves and reflects the ORIGINAL Kan weak equivalences.
Reuse exact original horn reversal, the actual self-adjunction and native Brown factorization.
-/
set_option autoImplicit false
open CategoryTheory Simplicial HomotopicalAlgebra
open DaggerOriginalHornReversal DaggerOriginalStandardSimplexReversal
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerNativeSimplicialOppositeKanWeak
noncomputable section

def hornArrowIso (n : ℕ) (i : Fin (n + 1)) :
    Arrow.mk (SSet.opFunctor.map (SSet.horn.{u} n i).ι) ≅
      Arrow.mk (SSet.horn.{u} n i.rev).ι :=
  Arrow.isoMk (hornReversalIso n i) (standardSimplexReversalIso n)
    (hornReversalHom_comp_ι n i)

theorem op_horn_lifting {X Y : SSet.{u}} (p : X ⟶ Y) [Fibration p]
    (n : ℕ) (i : Fin (n + 2)) :
    HasLiftingProperty (SSet.horn.{u} (n + 1) i).ι (SSet.opFunctor.map p) := by
  apply (SSet.opEquivalence.toAdjunction.hasLiftingProperty_iff
    (SSet.horn.{u} (n + 1) i).ι p).mp
  exact (HasLiftingProperty.iff_of_arrow_iso_left (hornArrowIso (n + 1) i) p).mpr
    inferInstance

theorem op_fibration {X Y : SSet.{u}} (p : X ⟶ Y) [Fibration p] :
    Fibration (SSet.opFunctor.map p) := by
  apply (SSet.modelCategoryQuillen.fibration_iff _).mpr
  intro A B j hj
  change (⨆ n : ℕ, MorphismProperty.ofHoms
    (fun i : Fin (n + 2) ↦ (SSet.horn.{u} (n + 1) i).ι)) j at hj
  rw [MorphismProperty.iSup_iff] at hj
  obtain ⟨n, hn⟩ := hj
  cases hn with
  | mk i => exact op_horn_lifting p n i

instance op_preservesFibrations : SSet.opFunctor.{u}.PreservesFibrations where
  fibration_map p := op_fibration p

instance inverse_preservesFibrations : SSet.opEquivalence.{u}.inverse.PreservesFibrations where
  fibration_map p := by
    intro hp
    have : Fibration p := hp
    change Fibration (SSet.opFunctor.map p)
    exact op_fibration p

instance op_preservesTrivialCofibrations : SSet.opFunctor.{u}.PreservesTrivialCofibrations :=
  SSet.opEquivalence.toAdjunction.preservesTrivialCofibrations_iff_preservesFibrations.mpr
    inferInstance

theorem op_weak {X Y : SSet.{u}} (f : X ⟶ Y) [WeakEquivalence f] :
    WeakEquivalence (SSet.opFunctor.map f) := by
  let h : CofibrantBrownFactorization f := Classical.choice inferInstance
  have hi := Functor.PreservesTrivialCofibrations.trivialCofibrations_le
    SSet.opFunctor.{u} h.i (mem_trivialCofibrations h.i)
  have hs := Functor.PreservesTrivialCofibrations.trivialCofibrations_le
    SSet.opFunctor.{u} h.s (mem_trivialCofibrations h.s)
  change trivialCofibrations SSet.{u} (SSet.opFunctor.map h.i) at hi
  change trivialCofibrations SSet.{u} (SSet.opFunctor.map h.s) at hs
  rw [mem_trivialCofibrations_iff] at hi hs
  have : WeakEquivalence (SSet.opFunctor.map h.i) := hi.2
  have : WeakEquivalence (SSet.opFunctor.map h.s) := hs.2
  have hsp : SSet.opFunctor.map h.s ≫ SSet.opFunctor.map h.p = 𝟙 (SSet.opFunctor.obj Y) := by
    rw [← Functor.map_comp, h.s_p, SSet.opFunctor.map_id]
  have : WeakEquivalence (SSet.opFunctor.map h.p) := weakEquivalence_of_precomp_of_fac hsp
  have hw : WeakEquivalence (SSet.opFunctor.map h.i ≫ SSet.opFunctor.map h.p) := inferInstance
  rwa [← Functor.map_comp, h.fac] at hw

theorem weak_op_iff {X Y : SSet.{u}} (f : X ⟶ Y) :
    WeakEquivalence (SSet.opFunctor.map f) ↔ WeakEquivalence f := by
  constructor
  · intro h
    have : WeakEquivalence (SSet.opFunctor.map f) := h
    have : WeakEquivalence (SSet.opFunctor.map (SSet.opFunctor.map f)) := op_weak _
    let ε := SSet.opFunctorCompOpFunctorIso.{u}
    have he : SSet.opFunctor.map (SSet.opFunctor.map f) ≫ (ε.app Y).hom =
        (ε.app X).hom ≫ f := ε.hom.naturality f
    have hc : WeakEquivalence
        (SSet.opFunctor.map (SSet.opFunctor.map f) ≫ (ε.app Y).hom) := inferInstance
    have : WeakEquivalence ((ε.app X).hom ≫ f) := he ▸ hc
    exact weakEquivalence_of_precomp (ε.app X).hom f
  · intro h
    have := h
    exact op_weak f

end
end DaggerNativeSimplicialOppositeKanWeak
