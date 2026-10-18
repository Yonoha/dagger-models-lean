import Mathlib.CategoryTheory.Limits.Types.Filtered
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
import TopCatModelCategory.TopCat.BoundaryClosedEmbeddings

/-! Original filtered cocone legs and their literal singular-realization maps. -/

open CategoryTheory Limits Opposite

universe u v w

namespace DaggerGeometricFilteredColimits

noncomputable section

/-- The original realization followed by the original singular functor. -/
def singRealization : SSet.{u} ⥤ SSet.{u} := SSet.toTop ⋙ TopCat.toSSet

/-- Every original leg is Mono, at arbitrary index universes, using actual eventual equality. -/
theorem cocone_leg_mono {J : Type v} [Category.{w} J] [Small.{u} J] [IsFiltered J]
    {D : J ⥤ SSet.{u}} {c : Cocone D} (hc : IsColimit c)
    (hmono : ∀ {a b : J} (f : a ⟶ b), Mono (D.map f)) (j : J) :
    Mono (c.ι.app j) := by
  have hq (q : SimplexCategoryᵒᵖ) : Mono ((c.ι.app j).app q) := by
    rw [mono_iff_injective]
    intro a b hab
    obtain ⟨k, f, hf⟩ := (Types.FilteredColimit.isColimit_eq_iff'
      (isColimitOfPreserves ((evaluation SimplexCategoryᵒᵖ (Type u)).obj q) hc)
      a b).1 hab
    letI : Mono (D.map f) := hmono f
    exact (mono_iff_injective ((D.map f).app q)).1 inferInstance hf
  letI (q : SimplexCategoryᵒᵖ) : Mono ((c.ι.app j).app q) := hq q
  exact NatTrans.mono_of_mono_app _

/-- Realization of the SAME original Mono is injective. -/
theorem realization_map_injective {X Y : SSet.{u}} (i : X ⟶ Y) [Mono i] :
    Function.Injective (SSet.toTop.map i) :=
  (SSet.closedEmbeddings_toObj_map_of_mono i).injective

/-- A singular simplex is the full original ULift Hom map, including its operators. -/
def singularSimplexEquiv (X : TopCat.{u}) (q : SimplexCategoryᵒᵖ) :
    (TopCat.toSSet.obj X).obj q ≃ (SimplexCategory.toTop.obj q.unop ⟶ X) :=
  Equiv.ulift

@[simp]
theorem singularSimplexEquiv_map {X Y : TopCat.{u}} (f : X ⟶ Y)
    (q : SimplexCategoryᵒᵖ) (a : (TopCat.toSSet.obj X).obj q) :
    singularSimplexEquiv Y q ((TopCat.toSSet.map f).app q a) =
      singularSimplexEquiv X q a ≫ f := rfl

/-- Mono realization cancels equality of entire continuous singular simplices. -/
theorem singRealization_map_app_injective {X Y : SSet.{u}} (i : X ⟶ Y) [Mono i]
    (q : SimplexCategoryᵒᵖ) : Function.Injective ((singRealization.map i).app q) := by
  intro a b hab
  apply (singularSimplexEquiv (SSet.toTop.obj X) q).injective
  ext z
  apply realization_map_injective i
  exact congrArg (fun t ↦ singularSimplexEquiv (SSet.toTop.obj Y) q t z) hab

end
end DaggerGeometricFilteredColimits
