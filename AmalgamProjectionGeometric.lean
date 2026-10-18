import AmalgamFirstStage

/-! Original product projections with specified contractible-factor points.
The other factor is arbitrary, including empty or non-Kan simplicial sets. -/

open CategoryTheory MonoidalCategory CartesianMonoidalCategory HomotopicalAlgebra
open DaggerAmalgamFirstStage DaggerOrdinaryAnodyneTensor
open scoped SSet.modelCategoryQuillen

universe u

set_option autoImplicit false

namespace DaggerAmalgamHomWeakEquivalence

noncomputable section

theorem atRight_fst (V R : SSet.{u}) (r : 𝟙_ SSet.{u} ⟶ R) :
    atRight V r ≫ fst V R = 𝟙 V := by
  ext q v
  rfl

theorem atLeft_snd (L V : SSet.{u}) (l : 𝟙_ SSet.{u} ⟶ L) :
    atLeft l V ≫ snd L V = 𝟙 V := by
  ext q v
  rfl

theorem atRight_anodyne (V R : SSet.{u}) (r : 𝟙_ SSet.{u} ⟶ R)
    (hr : SSet.anodyneExtensions r) : SSet.anodyneExtensions (atRight V r) :=
  SSet.anodyneExtensions.comp_mem _ _ (SSet.anodyneExtensions.of_isIso _)
    (whiskerLeft r hr V)

theorem fst_geometric (V R : SSet.{u}) (r : 𝟙_ SSet.{u} ⟶ R)
    (hR : SSet.KanComplex.W (TopCat.toSSet.map (SSet.toTop.map (toUnit R)))) :
    SSet.KanComplex.W (TopCat.toSSet.map (SSet.toTop.map (fst V R))) := by
  have hs := atRight_anodyne V R r (point_anodyne r hR)
  have : WeakEquivalence (atRight V r) :=
    ((mem_trivialCofibrations_iff _).1
      ((anodyne_iff_trivialCofibration _).1 hs)).2
  have : WeakEquivalence (atRight V r ≫ fst V R) := by
    rw [atRight_fst]
    infer_instance
  exact (DaggerModels.KanQuillenReuse.weakEquivalence_iff_geometric _).1
    (weakEquivalence_of_precomp (atRight V r) (fst V R))

theorem snd_geometric (L V : SSet.{u}) (l : 𝟙_ SSet.{u} ⟶ L)
    (hL : SSet.KanComplex.W (TopCat.toSSet.map (SSet.toTop.map (toUnit L)))) :
    SSet.KanComplex.W (TopCat.toSSet.map (SSet.toTop.map (snd L V))) := by
  have hs := atLeft_anodyne l V (point_anodyne l hL)
  have : WeakEquivalence (atLeft l V) :=
    ((mem_trivialCofibrations_iff _).1
      ((anodyne_iff_trivialCofibration _).1 hs)).2
  have : WeakEquivalence (atLeft l V ≫ snd L V) := by
    rw [atLeft_snd]
    infer_instance
  exact (DaggerModels.KanQuillenReuse.weakEquivalence_iff_geometric _).1
    (weakEquivalence_of_precomp (atLeft l V) (snd L V))

end
end DaggerAmalgamHomWeakEquivalence
