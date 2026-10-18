import OriginalEC2NondegenerateFreeOrbit
import TopCatModelCategory.TopCat.ToTopDecomposition

/-!
# Actual realized `EC₂` cells indexed by their free `C₂` orbit

The cells are those of the retained relative cell complex on the literal
codiscrete nerve, mapped by the actual geometric-realization functor.
No equivariant CW structure is asserted by these indexing results.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial HomotopicalAlgebra
open DaggerOriginalDaggerRealizationC2Action
open DaggerOriginalEC2SimplicialAction
open DaggerOriginalEC2NondegenerateFreeOrbit

universe u

namespace DaggerOriginalEC2RealizedCellOrbits

noncomputable section

private abbrev E : SSet.{u} := simplicialEC2.{u}

/-- A nondegenerate simplex has its actual dimension and a unique `C₂` label. -/
def nondegenerateIndexEquiv : E.{u}.N ≃ Σ _n : ℕ, C2.{u} :=
  { toFun s :=
      ⟨s.dim, (nondegenerateEquiv.{u} s.dim).symm
        ⟨s.simplex, s.nonDegenerate⟩⟩
    invFun p := SSet.N.mk (orbitMap.{u} p.1 p.2).val
      (orbitMap.{u} p.1 p.2).property
    left_inv := by
      intro s
      rcases SSet.N.mk_surjective s with ⟨n, ⟨x, hx⟩, rfl⟩
      change SSet.N.mk (X := E.{u}) (n := n)
        ((nondegenerateEquiv.{u} n) ((nondegenerateEquiv.{u} n).symm ⟨x, hx⟩)).val _ = _
      simp only [Equiv.apply_symm_apply]
    right_inv := by
      rintro ⟨n, g⟩
      change (⟨n, ((nondegenerateEquiv.{u} n).symm
        ((nondegenerateEquiv.{u} n) g))⟩ : Σ _n : ℕ, C2.{u}) = ⟨n, g⟩
      rw [Equiv.symm_apply_apply] }

/-- The genuine relative cell complex of the original codiscrete nerve,
mapped through the actual geometric-realization functor. -/
def realizedRelativeCellComplex :=
  E.{u}.relativeCellComplex.map SSet.toTop.{u}

/-- The realized cell index consists of its original dimension and one
element of the actual regular `C₂` orbit. -/
def realizedCellsEquiv : realizedRelativeCellComplex.{u}.Cells ≃
    Σ _n : ℕ, C2.{u} :=
  (E.{u}.relativeCellComplex.mapCellsEquiv SSet.toTop.{u}).trans
    ((E.{u}.relativeCellComplexCellsEquiv).trans nondegenerateIndexEquiv.{u})

/-- This reindexing does not change the dimension at which a cell is attached. -/
theorem realizedCellsEquiv_dim (c : realizedRelativeCellComplex.{u}.Cells) :
    (realizedCellsEquiv.{u} c).1 = c.j := rfl

/-- The characteristic map is the realization of the literal simplex whose
vertices are obtained by the original regular action. -/
theorem realizedCell_characteristic (n : ℕ) (g : C2.{u}) :
    ((realizedCellsEquiv.{u}).symm ⟨n, g⟩).ι =
      SSet.toTop.map ((SSet.yonedaEquiv (X := E.{u}) (n := ⦋n⦌)).symm
        (orbitMap.{u} n g).val) := by
  change ((E.{u}.relativeCellComplex.mapCellsEquiv SSet.toTop.{u}).symm
      ((E.{u}.relativeCellComplexCellsEquiv).symm
        (SSet.N.mk (orbitMap.{u} n g).val
          (orbitMap.{u} n g).property))).ι = _
  rw [RelativeCellComplex.ι_mapCellEquiv_symm]
  rw [SSet.relativeCellComplexι_eq]
  rfl

end

end DaggerOriginalEC2RealizedCellOrbits
