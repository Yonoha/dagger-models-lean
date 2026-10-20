import ActualInnerConeRightMappingContractible

/-! Actual right mappings from the first to the last vertex in every original standard simplex. -/
set_option autoImplicit false
open CategoryTheory Opposite Simplicial HomotopicalAlgebra
open DaggerActualGeneralRightConeMapping DaggerActualInnerConeIntervalComparison
open DaggerActualInnerConeRightMappingContractible
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerActualSimplexOuterMappingContractible
noncomputable section

def firstVertex (n : ℕ) : (Δ[n] : SSet.{u}).obj (op ⦋0⦌) :=
  SSet.stdSimplex.obj₀Equiv.symm (0 : Fin (n + 1))

def lastVertex (n : ℕ) : (Δ[n] : SSet.{u}).obj (op ⦋0⦌) :=
  SSet.stdSimplex.obj₀Equiv.symm (Fin.last n)

def outerOrder (n : ℕ) : ⦋1⦌ ⟶ ⦋n⦌ :=
  SimplexCategory.Hom.mk
    { toFun := fun i ↦ if i = 0 then 0 else Fin.last n
      monotone' := by
        intro i j hij
        fin_cases i <;> fin_cases j <;> simp_all }

def outerMap (n : ℕ) : (Δ[1] : SSet.{u}) ⟶ Δ[n] := SSet.stdSimplex.map (outerOrder n)

theorem outerMap_first (n : ℕ) :
    (outerMap.{u} n).app (op ⦋0⦌) zeroVertex = firstVertex n := rfl

theorem outerMap_last (n : ℕ) :
    (outerMap.{u} n).app (op ⦋0⦌) oneVertex = lastVertex n := rfl

def fromPoint (n : ℕ) : (Δ[0] : SSet.{u}) ⟶
    rightMapping (Δ[n] : SSet.{u}) (firstVertex n) (lastVertex n) where
  app q _ :=
    ⟨DaggerOriginalCounitRightConeContractibilityRetraction.projection q.unop.len ≫ outerMap n,
      by
        change (outerMap n).app (op ⦋0⦌)
          ((DaggerOriginalCounitRightConeContractibilityRetraction.projection q.unop.len).app
            (op ⦋0⦌) (DaggerOriginalCounitRightCone.alpha q.unop.len)) = _
        rw [projection_alpha_value, outerMap_first],
      by
        change (outerMap n).app (op ⦋0⦌)
          ((DaggerOriginalCounitRightConeContractibilityRetraction.projection q.unop.len).app
            (op ⦋0⦌) (DaggerOriginalCounitRightCone.omega q.unop.len)) = _
        rw [projection_omega_value, outerMap_last]⟩
  naturality q r α := by
    funext s
    exact Subsingleton.elim _ _

def outerMappingIso (n : ℕ) :
    rightMapping (Δ[n] : SSet.{u}) (firstVertex n) (lastVertex n) ≅ (Δ[0] : SSet.{u}) where
  hom := SSet.stdSimplex.isTerminalObj₀.from _
  inv := fromPoint n
  hom_inv_id := by
    apply NatTrans.ext
    funext q s
    exact Subsingleton.elim _ _
  inv_hom_id := SSet.stdSimplex.isTerminalObj₀.hom_ext _ _

theorem outer_mapping_point_weak (n : ℕ) : WeakEquivalence
    (SSet.stdSimplex.isTerminalObj₀.from
      (rightMapping (Δ[n] : SSet.{u}) (firstVertex n) (lastVertex n))) := by
  change WeakEquivalence (outerMappingIso n).hom
  infer_instance

end
end DaggerActualSimplexOuterMappingContractible
