import FilteredGeometricCocone
import TopCatModelCategory.SSet.Presentable
import Mathlib.CategoryTheory.Presentable.Finite

/-! The ORIGINAL Nat diagrams at every u; no reindexing or fixed-object surrogate. -/

open CategoryTheory Limits Opposite

universe u

namespace DaggerGeometricFilteredColimits
noncomputable section

attribute [local instance] Cardinal.fact_isRegular_aleph0

/-- Generalize only the accepted finite-factor pattern to the supplied original SSet Nat cocone. -/
theorem exists_compact_factor_nat {D : ℕ ⥤ SSet.{u}} {c : Cocone D} (hc : IsColimit c)
    {K : TopCat.{u}} [CompactSpace K] (α : K ⟶ SSet.toTop.obj c.pt) :
    ∃ (n : ℕ) (β : K ⟶ SSet.toTop.obj (D.obj n)),
      β ≫ SSet.toTop.map (c.ι.app n) = α := by
  obtain ⟨A, hA, g, hg⟩ := SSet.exists_factor_thru_finite_of_topCatHom α
  letI : A.toSSet.IsFinite := hA
  letI : IsCardinalPresentable A.toSSet Cardinal.aleph0.{u} := inferInstance
  letI : LocallySmall.{u} ℕ := locallySmall_of_thin
  letI : EssentiallySmall.{u} ℕ := inferInstance
  letI : IsCardinalFiltered ℕ Cardinal.aleph0.{u} :=
    (isCardinalFiltered_aleph0_iff ℕ).2 inferInstance
  obtain ⟨n, i, hi⟩ := IsCardinalPresentable.exists_hom_of_isColimit Cardinal.aleph0.{u}
    hc A.ι
  refine ⟨n, g ≫ SSet.toTop.map i, ?_⟩
  rw [Category.assoc, ← SSet.toTop.map_comp, hi]
  exact hg.symm

def simplexFactorNat {D : ℕ ⥤ SSet.{u}} {c : Cocone D} (hc : IsColimit c) :
    SimplexFactor c := by
  intro q α
  have : CompactSpace (SimplexCategory.toTop.{u}.obj q.unop) := simplex_compact q
  exact exists_compact_factor_nat hc α

/-- Full degree UP with original Nat stages and legs at arbitrary u. -/
def singRealizationNatDegreeIsColimit {D : ℕ ⥤ SSet.{u}} {c : Cocone D}
    (hc : IsColimit c) (hmono : ∀ {a b : ℕ} (f : a ⟶ b), Mono (D.map f))
    (q : SimplexCategoryᵒᵖ) :
    IsColimit (((evaluation SimplexCategoryᵒᵖ (Type u)).obj q).mapCocone
      (singRealization.mapCocone c)) :=
  singRealizationDegreeIsColimitOfFactor hc hmono (simplexFactorNat hc) q

/-- Full simplicial UP of the same original Nat mapped cocone, not a different index type. -/
def singRealizationNatIsColimit {D : ℕ ⥤ SSet.{u}} {c : Cocone D} (hc : IsColimit c)
    (hmono : ∀ {a b : ℕ} (f : a ⟶ b), Mono (D.map f)) :
    IsColimit (singRealization.mapCocone c) :=
  singRealizationIsColimitOfFactor hc hmono (simplexFactorNat hc)

end
end DaggerGeometricFilteredColimits
