import ArrowCardinalLocalPresentability

/-! Presentations in the original Arrow category use the SAME cardinal rank. -/
set_option autoImplicit false
open CategoryTheory Limits
universe u v w
namespace DaggerOriginalArrowFilteredPresentations

theorem exists_presentation {C : Type w} [Category.{v} C]
    (κ : Cardinal.{u}) [Fact κ.IsRegular] [IsCardinalLocallyPresentable.{u} (Arrow C) κ]
    (X : Arrow C) :
    ∃ (J : Type u) (_ : SmallCategory J) (_ : IsCardinalFiltered J κ)
      (F : J ⥤ Arrow C) (ι : F ⟶ (Functor.const J).obj X),
      Nonempty (IsColimit (Cocone.mk X ι)) ∧ ∀ j, IsCardinalPresentable (F.obj j) κ := by
  obtain ⟨P, _, hP⟩ := HasCardinalFilteredGenerator.exists_generator (Arrow C) κ
  obtain ⟨J, _, _, ⟨p⟩⟩ := hP.exists_colimitsOfShape X
  refine ⟨J, inferInstance, inferInstance, p.diag, p.ι, ⟨p.isColimit⟩, ?_⟩
  intro j
  exact (isCardinalPresentable_iff _ _).1 (hP.le_isCardinalPresentable _ (p.prop_diag_obj j))

end DaggerOriginalArrowFilteredPresentations
