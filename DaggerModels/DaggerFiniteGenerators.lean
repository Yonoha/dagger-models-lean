import DaggerModels.DaggerSimplicialFilteredColimits
import DaggerModels.StrongGeneratorAdjunction
import Mathlib.CategoryTheory.Presentable.Adjunction

/-!
A `u`-small strong generator of finitely presentable
dagger simplicial categories. Free images of graph generators are essentially
small; small representatives are selected before claiming smallness. Local
finite presentability below is conditional on all `u`-small colimits existing.
-/

open CategoryTheory Limits

universe u v w

attribute [local instance] Cardinal.fact_isRegular_aleph0

namespace DaggerModels.DaggerSimplicialCat

/-- Choosing representatives up to isomorphism preserves the strong-generator property. -/
theorem strongGenerator_of_le_isoClosure {C : Type v} [Category.{w} C]
    {P Q : ObjectProperty C} (hP : P.IsStrongGenerator) (hPQ : P ≤ Q.isoClosure) :
    Q.IsStrongGenerator := by
  rw [ObjectProperty.isStrongGenerator_iff]
  refine ⟨?_, fun X Y i _ hi ↦ ?_⟩
  · intro X Y f g h
    apply hP.isSeparating
    intro A hA k
    obtain ⟨B, hB, ⟨e⟩⟩ := hPQ A hA
    have he := h B hB (e.inv ≫ k)
    exact (cancel_epi e.inv).1 (by simpa only [Category.assoc] using he)
  · exact hP.isIso_of_mono i (fun A hA k ↦ by
      obtain ⟨B, hB, ⟨e⟩⟩ := hPQ A hA
      obtain ⟨f, hf⟩ := hi B hB (e.inv ≫ k)
      refine ⟨e.hom ≫ f, ?_⟩
      change (e.hom ≫ f) ≫ i = k
      change f ≫ i = e.inv ≫ k at hf
      rw [Category.assoc, hf, e.hom_inv_id_assoc])

/-- No category colimit premise is needed for a small strong generator of FP objects. -/
theorem exists_small_finitelyPresentableStrongGenerator :
    ∃ (P : ObjectProperty DaggerSimplicialCat.{u, u}) (_ : ObjectProperty.Small.{u} P),
      P.IsStrongGenerator ∧ P ≤ isCardinalPresentable DaggerSimplicialCat.{u, u}
        Cardinal.aleph0.{u} := by
  let : HasColimits DaggerSimplicialGraph.{u} := daggerGraphHasColimits
  let : IsLocallyFinitelyPresentable.{u} DaggerSimplicialGraph.{u} :=
    daggerGraphLocallyFinitelyPresentable
  let : forgetGraph.{u}.IsCardinalAccessible Cardinal.aleph0.{u} :=
    forgetGraphIsCardinalAccessibleAleph0
  obtain ⟨P, hPsmall, hPstrong, hPfp⟩ :=
    (IsCardinalLocallyPresentable.iff_exists_isStrongGenerator
      DaggerSimplicialGraph.{u} Cardinal.aleph0.{u}).1 inferInstance
  let R := P.map FreeDaggerSimplicialCategory.functor
  have hRstrong : R.IsStrongGenerator :=
    AdjunctionStrongGenerator.freeDaggerSimplicialCategory hPstrong
  have hRfp : R ≤ isCardinalPresentable DaggerSimplicialCat.{u, u} Cardinal.aleph0.{u} := by
    rintro Y ⟨X, hX, ⟨e⟩⟩
    let : IsCardinalPresentable X Cardinal.aleph0.{u} := hPfp X hX
    let : IsCardinalPresentable (FreeDaggerSimplicialCategory.functor.obj X)
        Cardinal.aleph0.{u} :=
      FreeDaggerSimplicialCategory.adjunction.isCardinalPresentable_leftAdjoint_obj
        Cardinal.aleph0 X
    exact isCardinalPresentable_of_iso e Cardinal.aleph0
  obtain ⟨Q, hQsmall, hQR, hRQ⟩ := ObjectProperty.EssentiallySmall.exists_small_le.{u} R
  exact ⟨Q, hQsmall, strongGenerator_of_le_isoClosure hRstrong hRQ, hQR.trans hRfp⟩

/-- The small strong generator gives LFP whenever all small colimits exist. -/
theorem locallyFinitelyPresentable_of_hasColimits
    [HasColimitsOfSize.{u, u} DaggerSimplicialCat.{u, u}] :
    IsLocallyFinitelyPresentable.{u} DaggerSimplicialCat.{u, u} :=
  (IsCardinalLocallyPresentable.iff_exists_isStrongGenerator
    DaggerSimplicialCat.{u, u} Cardinal.aleph0.{u}).2
      exists_small_finitelyPresentableStrongGenerator

end DaggerModels.DaggerSimplicialCat
