import TopCatModelCategory.SSet.FactorThruFinite
import TopCatModelCategory.SSet.Presentable
import Mathlib.CategoryTheory.Presentable.Finite
import Mathlib.Topology.Category.TopCat.Sphere

open CategoryTheory Limits

universe u

namespace DaggerCompactFilteredFactor

variable {J : Type u} [SmallCategory J] [IsFiltered J]
  {D : J ⥤ SSet.{u}} {c : Cocone D}

/-- A compact map into the same realized filtered colimit factors through one actual stage. -/
theorem exists_factor_of_compact (hc : IsColimit c) {K : TopCat.{u}} [CompactSpace K]
    (α : K ⟶ SSet.toTop.obj c.pt) :
    ∃ (j : J) (β : K ⟶ SSet.toTop.obj (D.obj j)),
      β ≫ SSet.toTop.map (c.ι.app j) = α := by
  obtain ⟨A, hA, g, hg⟩ := SSet.exists_factor_thru_finite_of_topCatHom α
  have : A.toSSet.IsFinite := hA
  obtain ⟨j, i, hi⟩ := IsFinitelyPresentable.exists_hom_of_isColimit hc A.ι
  refine ⟨j, g ≫ SSet.toTop.map i, ?_⟩
  rw [Category.assoc, ← SSet.toTop.map_comp, hi]
  exact hg.symm

/-- Every original sphere dimension, including zero, uses the same cocone legs. -/
theorem exists_factor_of_sphere (hc : IsColimit c) (m : ℕ)
    (α : TopCat.sphere.{u} m ⟶ SSet.toTop.obj c.pt) :
    ∃ (j : J) (β : TopCat.sphere.{u} m ⟶ SSet.toTop.obj (D.obj j)),
      β ≫ SSet.toTop.map (c.ι.app j) = α := by
  have : CompactSpace (TopCat.sphere.{u} m) := by
    change CompactSpace (TopCat.diskBoundary.{u} (m + 1))
    infer_instance
  exact exists_factor_of_compact hc α

end DaggerCompactFilteredFactor
