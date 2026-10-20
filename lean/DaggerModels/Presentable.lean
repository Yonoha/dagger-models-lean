import DaggerModels.Presheaf
import Mathlib.CategoryTheory.Presentable.Type
import Mathlib.CategoryTheory.Presentable.Presheaf
import Mathlib.CategoryTheory.Presentable.Adjunction

/-!
# Completeness, cocompleteness, and presentability of dagger simplicial sets

The presheaf equivalence transports all small limits and colimits. For local
presentability, the singleton type is a strong generator of `Type u`; its
free representables form a small strong generator of reversal presheaves.
The cardinal and diagram universe in these results is `u`, including when
the reversal simplex category itself lives in universe zero.
-/

open CategoryTheory Limits Opposite

universe u

namespace DaggerModels

/-- The singleton type is a strong generator of the category of `u`-small types. -/
theorem typeUnitStrongGenerator :
    (ObjectProperty.singleton PUnit.{u + 1}).IsStrongGenerator := by
  rw [ObjectProperty.isStrongGenerator_iff]
  refine ⟨?_, ?_⟩
  · intro X Y f g h
    funext x
    exact congrFun (h PUnit (by simp) (fun _ ↦ x)) PUnit.unit
  · intro X Y i _ h
    apply (isIso_iff_bijective i).2
    refine ⟨injective_of_mono i, ?_⟩
    intro y
    obtain ⟨f, hf⟩ := h PUnit (by simp) (fun _ ↦ y)
    exact ⟨f PUnit.unit, congrFun hf PUnit.unit⟩

/-- The category of `u`-small types is locally finitely presentable. -/
theorem typesLocallyFinitelyPresentable :
    IsLocallyFinitelyPresentable.{u} (Type u) := by
  let : Fact (Cardinal.aleph0.{u}).IsRegular := Cardinal.fact_isRegular_aleph0
  apply (IsCardinalLocallyPresentable.iff_exists_isStrongGenerator
    (Type u) Cardinal.aleph0).2
  refine ⟨ObjectProperty.singleton PUnit.{u + 1}, inferInstance,
    typeUnitStrongGenerator, ?_⟩
  rw [ObjectProperty.singleton_le_iff, isCardinalPresentable_iff]
  exact (hasCardinalLT_of_finite PUnit.{u + 1} Cardinal.aleph0 le_rfl).isCardinalPresentable

/-- Reversal presheaves valued in `Type u` are locally finitely presentable. -/
theorem reversalPresheavesLocallyFinitelyPresentable :
    IsLocallyFinitelyPresentable.{u} (ReverseSimplexᵒᵖ ⥤ Type u) := by
  let : Fact (Cardinal.aleph0.{u}).IsRegular := Cardinal.fact_isRegular_aleph0
  let P : ObjectProperty (Type u) := ObjectProperty.singleton PUnit.{u + 1}
  let G := ObjectProperty.ofObj (fun (T : ReverseSimplex × Subtype P) ↦
    Presheaf.freeYoneda T.1 T.2.1)
  apply (IsCardinalLocallyPresentable.iff_exists_isStrongGenerator
    (ReverseSimplexᵒᵖ ⥤ Type u) Cardinal.aleph0).2
  refine ⟨G, inferInstance,
    Presheaf.isStrongGenerator (A := Type u) typeUnitStrongGenerator.{u} ReverseSimplex, ?_⟩
  rintro _ ⟨n, M, hM⟩
  have hM' : IsCardinalPresentable M Cardinal.aleph0 := by
    obtain rfl : PUnit.{u + 1} = M := by simpa [P] using hM
    exact (hasCardinalLT_of_finite PUnit.{u + 1} Cardinal.aleph0 le_rfl).isCardinalPresentable
  rw [isCardinalPresentable_iff]
  infer_instance

/-- Dagger simplicial sets admit all `u`-small limits. -/
theorem daggerSSetHasLimits : HasLimits DaggerSSet.{u} :=
  Adjunction.has_limits_of_equivalence daggerSSetEquivalencePresheaf.functor

/-- Dagger simplicial sets admit all `u`-small colimits. -/
theorem daggerSSetHasColimits : HasColimits DaggerSSet.{u} :=
  Adjunction.has_colimits_of_equivalence daggerSSetEquivalencePresheaf.functor

/-- Dagger simplicial sets are locally finitely presentable at their value universe. -/
theorem daggerSSetLocallyFinitelyPresentable :
    IsLocallyFinitelyPresentable.{u} DaggerSSet.{u} := by
  let : IsLocallyFinitelyPresentable.{u} (ReverseSimplexᵒᵖ ⥤ Type u) :=
    reversalPresheavesLocallyFinitelyPresentable
  let : Fact (Cardinal.aleph0.{u}).IsRegular := Cardinal.fact_isRegular_aleph0
  exact daggerSSetEquivalencePresheaf.symm.isCardinalLocallyPresentable Cardinal.aleph0

/-- Dagger simplicial sets are locally presentable at their value universe. -/
theorem daggerSSetLocallyPresentable : IsLocallyPresentable.{u} DaggerSSet.{u} := by
  let : Fact (Cardinal.aleph0.{u}).IsRegular := Cardinal.fact_isRegular_aleph0
  exact ⟨Cardinal.aleph0, inferInstance, daggerSSetLocallyFinitelyPresentable⟩

end DaggerModels
