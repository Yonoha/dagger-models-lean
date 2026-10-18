import FilteredGeometricLegs
import CompactFilteredFactor

/-! Complete UP of the SAME singular-realization mapped cocone, from compact factorization. -/

open CategoryTheory Limits Opposite

universe u v w

namespace DaggerGeometricFilteredColimits
noncomputable section

theorem simplex_compact (q : SimplexCategoryᵒᵖ) :
    CompactSpace (SimplexCategory.toTop.{u}.obj q.unop) := by
  change CompactSpace (ULift.{u} (stdSimplex ℝ (Fin (q.unop.len + 1))))
  infer_instance

variable {J : Type v} [Category.{w} J]
variable {D : J ⥤ SSet.{u}} {c : Cocone D}

/-- Only an internal factorization predicate; the full common-u and Nat exports discharge it. -/
def SimplexFactor (c : Cocone D) : Prop :=
  ∀ (q : SimplexCategoryᵒᵖ) (α : SimplexCategory.toTop.obj q.unop ⟶ SSet.toTop.obj c.pt),
    ∃ (j : J) (β : SimplexCategory.toTop.obj q.unop ⟶ SSet.toTop.obj (D.obj j)),
      β ≫ SSet.toTop.map (c.ι.app j) = α

@[simp]
theorem singRealization_leg (c : Cocone D) (j : J) :
    (singRealization.mapCocone c).ι.app j =
      TopCat.toSSet.map (SSet.toTop.map (c.ι.app j)) := rfl

/-- Every entire original singular simplex comes through an actual original leg. -/
theorem singular_degree_surjective (factor : SimplexFactor c) (q : SimplexCategoryᵒᵖ)
    (a : (singRealization.obj c.pt).obj q) :
    ∃ (j : J) (b : (singRealization.obj (D.obj j)).obj q),
      a = (singRealization.map (c.ι.app j)).app q b := by
  obtain ⟨j, β, hβ⟩ := factor q (singularSimplexEquiv _ q a)
  refine ⟨j, (singularSimplexEquiv _ q).symm β, ?_⟩
  apply (singularSimplexEquiv _ q).injective
  change singularSimplexEquiv _ q a =
    singularSimplexEquiv _ q ((TopCat.toSSet.map (SSet.toTop.map (c.ι.app j))).app q _)
  rw [singularSimplexEquiv_map, Equiv.apply_symm_apply]
  exact hβ.symm

variable [Small.{u} J] [IsFiltered J]

/-- Full degreewise arbitrary-target UP, with SAME-stage injection and identity arrow. -/
def singRealizationDegreeIsColimitOfFactor (hc : IsColimit c)
    (hmono : ∀ {a b : J} (f : a ⟶ b), Mono (D.map f)) (factor : SimplexFactor c)
    (q : SimplexCategoryᵒᵖ) :
    IsColimit (((evaluation SimplexCategoryᵒᵖ (Type u)).obj q).mapCocone
      (singRealization.mapCocone c)) := by
  refine Types.FilteredColimit.isColimitOf' _ _
    (singular_degree_surjective factor q) ?_
  intro j a b hab
  letI : Mono (c.ι.app j) := cocone_leg_mono hc hmono j
  refine ⟨j, 𝟙 j, ?_⟩
  have h := singRealization_map_app_injective (c.ι.app j) q hab
  simpa using h

/-- Full simplicial desc/fac/uniq and all operator naturality, not only pointwise counts. -/
def singRealizationIsColimitOfFactor (hc : IsColimit c)
    (hmono : ∀ {a b : J} (f : a ⟶ b), Mono (D.map f)) (factor : SimplexFactor c) :
    IsColimit (singRealization.mapCocone c) :=
  evaluationJointlyReflectsColimits _
    (singRealizationDegreeIsColimitOfFactor hc hmono factor)

/-- The SAME universal map for every arbitrary original target cocone. -/
def singRealizationDescOfFactor (hc : IsColimit c)
    (hmono : ∀ {a b : J} (f : a ⟶ b), Mono (D.map f)) (factor : SimplexFactor c)
    (s : Cocone (D ⋙ singRealization)) : singRealization.obj c.pt ⟶ s.pt :=
  (singRealizationIsColimitOfFactor hc hmono factor).desc s

theorem singRealizationDescOfFactor_fac (hc : IsColimit c)
    (hmono : ∀ {a b : J} (f : a ⟶ b), Mono (D.map f)) (factor : SimplexFactor c)
    (s : Cocone (D ⋙ singRealization)) (j : J) :
    singRealization.map (c.ι.app j) ≫ singRealizationDescOfFactor hc hmono factor s =
      s.ι.app j :=
  (singRealizationIsColimitOfFactor hc hmono factor).fac s j

theorem singRealizationDescOfFactor_uniq (hc : IsColimit c)
    (hmono : ∀ {a b : J} (f : a ⟶ b), Mono (D.map f)) (factor : SimplexFactor c)
    (s : Cocone (D ⋙ singRealization)) (m : singRealization.obj c.pt ⟶ s.pt)
    (hm : ∀ j, singRealization.map (c.ι.app j) ≫ m = s.ι.app j) :
    m = singRealizationDescOfFactor hc hmono factor s :=
  (singRealizationIsColimitOfFactor hc hmono factor).uniq s m hm

/-- Compact finite support discharges the internal predicate for the SAME common-u cocone. -/
def simplexFactor {J : Type u} [SmallCategory J] [IsFiltered J]
    {D : J ⥤ SSet.{u}} {c : Cocone D} (hc : IsColimit c) : SimplexFactor c := by
  intro q α
  have : CompactSpace (SimplexCategory.toTop.{u}.obj q.unop) := simplex_compact q
  exact DaggerCompactFilteredFactor.exists_factor_of_compact hc α

def singRealizationDegreeIsColimit {J : Type u} [SmallCategory J] [IsFiltered J]
    {D : J ⥤ SSet.{u}} {c : Cocone D} (hc : IsColimit c)
    (hmono : ∀ {a b : J} (f : a ⟶ b), Mono (D.map f)) (q : SimplexCategoryᵒᵖ) :
    IsColimit (((evaluation SimplexCategoryᵒᵖ (Type u)).obj q).mapCocone
      (singRealization.mapCocone c)) :=
  singRealizationDegreeIsColimitOfFactor hc hmono (simplexFactor hc) q

def singRealizationIsColimit {J : Type u} [SmallCategory J] [IsFiltered J]
    {D : J ⥤ SSet.{u}} {c : Cocone D} (hc : IsColimit c)
    (hmono : ∀ {a b : J} (f : a ⟶ b), Mono (D.map f)) :
    IsColimit (singRealization.mapCocone c) :=
  singRealizationIsColimitOfFactor hc hmono (simplexFactor hc)

end
end DaggerGeometricFilteredColimits
