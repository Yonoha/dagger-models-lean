import FilteredGeometricNat
import TopCatModelCategory.SSet.KanComplexWColimits
import TopCatModelCategory.TopCat.HornDeformationRetract

/-! Geometric W of the SAME supplied colimit comparison, common-u and ORIGINAL Nat. -/

open CategoryTheory Limits HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

universe u v w

namespace DaggerGeometricFilteredColimits
noncomputable section

/-- Every original SSet has a genuinely Kan singular realization. -/
theorem singRealization_fibrant (X : SSet.{u}) : IsFibrant (singRealization.obj X) := by
  change IsFibrant (TopCat.toSSet.obj (SSet.toTop.obj X))
  infer_instance

/-- Literal original geometric semantics; no replacement weak-equivalence predicate. -/
theorem singRealization_map_eq {X Y : SSet.{u}} (g : X ⟶ Y) :
    singRealization.map g = TopCat.toSSet.map (SSet.toTop.map g) := rfl

/-- Internal general bridge: both full mapped UPs are built here from the actual factors. -/
theorem geometric_of_colimit_factor {J : Type v} [Category.{w} J]
    [Small.{u} J] [LocallySmall.{u} J] [IsFiltered J]
    {D E : J ⥤ SSet.{u}} {c : Cocone D} {e : Cocone E}
    (hc : IsColimit c) (he : IsColimit e)
    (hD : ∀ {a b : J} (f : a ⟶ b), Mono (D.map f))
    (hE : ∀ {a b : J} (f : a ⟶ b), Mono (E.map f))
    (factorD : SimplexFactor c) (factorE : SimplexFactor e)
    (η : D ⟶ E) (g : c.pt ⟶ e.pt)
    (hlegs : ∀ j, c.ι.app j ≫ g = η.app j ≫ e.ι.app j)
    (hη : ∀ j, SSet.KanComplex.W (TopCat.toSSet.map (SSet.toTop.map (η.app j)))) :
    SSet.KanComplex.W (TopCat.toSSet.map (SSet.toTop.map g)) := by
  apply (MorphismProperty.colimitsOfShape_le
    (W := SSet.KanComplex.W) (J := J)) (singRealization.map g)
  refine MorphismProperty.colimitsOfShape.mk' (D ⋙ singRealization)
    (E ⋙ singRealization) (singRealization.mapCocone c) (singRealization.mapCocone e)
    (singRealizationIsColimitOfFactor hc hD factorD)
    (singRealizationIsColimitOfFactor he hE factorE)
    (Functor.whiskerRight η singRealization) hη (singRealization.map g) ?_
  intro j
  change singRealization.map (c.ι.app j) ≫ singRealization.map g =
    singRealization.map (η.app j) ≫ singRealization.map (e.ι.app j)
  rw [← Functor.map_comp, ← Functor.map_comp, hlegs j]

/-- COMPLETE E6: arbitrary original common-u filtered diagram, cocones, eta and SAME g. -/
theorem geometric_of_filtered_mono {J : Type u} [SmallCategory J] [IsFiltered J]
    {D E : J ⥤ SSet.{u}} {c : Cocone D} {e : Cocone E}
    (hc : IsColimit c) (he : IsColimit e)
    (hD : ∀ {a b : J} (f : a ⟶ b), Mono (D.map f))
    (hE : ∀ {a b : J} (f : a ⟶ b), Mono (E.map f))
    (η : D ⟶ E) (g : c.pt ⟶ e.pt)
    (hlegs : ∀ j, c.ι.app j ≫ g = η.app j ≫ e.ι.app j)
    (hη : ∀ j, SSet.KanComplex.W (TopCat.toSSet.map (SSet.toTop.map (η.app j)))) :
    SSet.KanComplex.W (TopCat.toSSet.map (SSet.toTop.map g)) :=
  geometric_of_colimit_factor hc he hD hE (simplexFactor hc) (simplexFactor he)
    η g hlegs hη

/-- COMPLETE E6-Nat at EVERY u, retaining the ORIGINAL Nat diagrams and every original leg. -/
theorem geometric_of_nat_mono {D E : ℕ ⥤ SSet.{u}} {c : Cocone D} {e : Cocone E}
    (hc : IsColimit c) (he : IsColimit e)
    (hD : ∀ {a b : ℕ} (f : a ⟶ b), Mono (D.map f))
    (hE : ∀ {a b : ℕ} (f : a ⟶ b), Mono (E.map f))
    (η : D ⟶ E) (g : c.pt ⟶ e.pt)
    (hlegs : ∀ n, c.ι.app n ≫ g = η.app n ≫ e.ι.app n)
    (hη : ∀ n, SSet.KanComplex.W (TopCat.toSSet.map (SSet.toTop.map (η.app n)))) :
    SSet.KanComplex.W (TopCat.toSSet.map (SSet.toTop.map g)) := by
  letI : LocallySmall.{u} ℕ := locallySmall_of_thin
  exact geometric_of_colimit_factor hc he hD hE (simplexFactorNat hc)
    (simplexFactorNat he) η g hlegs hη

end
end DaggerGeometricFilteredColimits
