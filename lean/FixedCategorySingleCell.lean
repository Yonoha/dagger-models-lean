import FixedCategoryPlacementComparison
import DaggerCellHomTransfer
import FixedCategoryHomTransfinite

set_option autoImplicit false

/-! Apply the existing original-cell theorem to the same fixed-object free placements. -/

open CategoryTheory Limits HomotopicalAlgebra DaggerModels
open scoped SSet.modelCategoryQuillen
open DaggerFixedCategoryAdjunction DaggerFixedGraphGenerators
open DaggerFixedCategoryPlacementComparison

universe u

namespace DaggerFixedCategorySingleCell

noncomputable section

section Single

variable {O : Type u} (s : Position O) {K L : SSet.{u}} (i : K ⟶ L)
  {C D : FixedDaggerSimplicialCat O} (a : freePlaced s K ⟶ C) (b : freePlaced s L ⟶ D)
  (f : C ⟶ D) (sq : IsPushout ((free O).map ((placement O s).map i)) a b f)

include sq

/-- The whole original Hom map is monic, including the diagonal placement. -/
theorem placed_cell_hom_mono [Mono i] : ∀ x y : O, Mono (f.val.map x y) :=
  DaggerCellHomTransfer.dagger_cell_hom_mono i (beta s K ≫ a.val)
    (cellPushout s i a b f sq)

variable [Mono i]
  (hi : SSet.KanComplex.W (TopCat.toSSet.map (SSet.toTop.map i)))

include hi

/-- The same original inclusion has anodyne maps on every original Hom. -/
theorem placed_cell_hom_anodyne : ∀ x y : O, SSet.anodyneExtensions (f.val.map x y) :=
  DaggerCellHomTransfer.dagger_cell_hom_anodyne i (beta s K ≫ a.val)
    (cellPushout s i a b f sq) hi

/-- The already defined all-Hom property is evaluated on the same original f. -/
theorem placed_cell_Q : DaggerFixedCategoryHomTransfinite.Q O f :=
  (DaggerFixedCategoryHomTransfinite.Q_iff_original O f).2
    (placed_cell_hom_anodyne s i a b f sq hi)

/-- The geometric conclusion retains the original realization-singular predicate. -/
theorem placed_cell_hom_geometric : ∀ x y : O,
    SSet.KanComplex.W (TopCat.toSSet.map (SSet.toTop.map (f.val.map x y))) :=
  DaggerCellHomTransfer.dagger_cell_hom_geometric i (beta s K ≫ a.val)
    (cellPushout s i a b f sq) hi

end Single

variable {O : Type u} (s : Position O)

/-- Every positive original horn, at either kind of original position. -/
theorem horn_pushout_Q (n : ℕ) (j : Fin (n + 2))
    {C D : FixedDaggerSimplicialCat O}
    (a : freePlaced s (SSet.horn.{u} (n + 1) j) ⟶ C)
    (b : freePlaced s (SSet.stdSimplex.{u}.obj (SimplexCategory.mk (n + 1))) ⟶ D) (f : C ⟶ D)
    (sq : IsPushout ((free O).map ((placement O s).map
      (SSet.horn.{u} (n + 1) j).ι)) a b f) : DaggerFixedCategoryHomTransfinite.Q O f := by
  apply placed_cell_Q s _ a b f sq
  apply (KanQuillenReuse.weakEquivalence_iff_geometric _).1
  exact ((mem_trivialCofibrations_iff _).1
    ((DaggerOrdinaryAnodyneTensor.anodyne_iff_trivialCofibration _).1
      (SSet.anodyneExtensions.horn_ι_mem n j))).2

/-- Unpack the literal J family and every original pushout, with no chosen-apex restriction. -/
theorem J_pushouts_le_Q (O : Type u) :
    (DaggerFixedCategoryGenerators.J O).pushouts ≤ DaggerFixedCategoryHomTransfinite.Q O := by
  rintro C D f ⟨A, B, p, a, b, hp, sq⟩
  rcases hp with ⟨⟨s, n, j⟩⟩
  exact horn_pushout_Q s n j a b f sq.flip

end

end DaggerFixedCategorySingleCell
