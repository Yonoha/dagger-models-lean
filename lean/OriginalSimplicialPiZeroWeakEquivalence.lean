import OriginalFixedObjectAmbientDaggerModel

/-!
# Exact simplicial connected components of an arbitrary native weak equivalence

Use the existing realization/singular description of the native weak class.
The singular map induces a bijection on components; both adjunction units do
so as well. Naturality transfers that bijection to the original simplicial map,
without assuming the original source or target is Kan.
-/
set_option autoImplicit false
open CategoryTheory HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerOriginalSimplicialPiZeroWeakEquivalence

/-- Every actual simplicial weak equivalence induces a bijection on actual components. -/
theorem bijective_mapPiZero {X Y : SSet.{u}} (f : X ⟶ Y) [WeakEquivalence f] :
    Function.Bijective (SSet.mapπ₀ f) := by
  have ht : WeakEquivalence (SSet.toTop.map f) :=
    (SSet.modelCategoryQuillen.weakEquivalence_iff f).1 inferInstance
  have hs := SSet.KanComplex.W.bijective_mapπ₀
    ((TopCat.modelCategory.weakEquivalence_iff (SSet.toTop.map f)).1 ht)
  have hx := SSet.bijective_mapπ₀_sSetTopAdj_unit_app X
  have hy := SSet.bijective_mapπ₀_sSetTopAdj_unit_app Y
  have hn (a : X.π₀) :
      SSet.mapπ₀ (TopCat.toSSet.map (SSet.toTop.map f))
          (SSet.mapπ₀ (sSetTopAdj.unit.app X) a) =
        SSet.mapπ₀ (sSetTopAdj.unit.app Y) (SSet.mapπ₀ f a) := by
    simpa only [SSet.mapπ₀_comp_apply] using
      (congrArg (fun k ↦ SSet.mapπ₀ k a) (sSetTopAdj.unit.naturality f)).symm
  constructor
  · intro a b hab
    apply hx.1
    apply hs.1
    rw [hn a, hn b, hab]
  · intro b
    obtain ⟨c, hc⟩ := hs.2 (SSet.mapπ₀ (sSetTopAdj.unit.app Y) b)
    obtain ⟨a, ha⟩ := hx.2 c
    refine ⟨a, hy.1 ?_⟩
    rw [← hn a, ha, hc]

end DaggerOriginalSimplicialPiZeroWeakEquivalence
