import ActualRightConeFinalEdgeNativeReuse
import ActualRightConeProjectionNaturality
import ActualInnerReplacementExtensions
import ActualRightMappingWeakInvariance
import NativeQuasicategoryOpposite
import Mathlib.AlgebraicTopology.Quasicategory.Nerve

/-! The SAME inner replacement of each original cone compares weakly to the original interval. -/
set_option autoImplicit false
open CategoryTheory Opposite Simplicial HomotopicalAlgebra
open DaggerOriginalCounitRightCone DaggerOriginalCounitRightConeFunctor
open DaggerActualRightConeFinalEdgeMaps DaggerActualRightConeFinalEdgeWeak
open DaggerActualRightConeProjectionNaturality DaggerActualRightConeFinalEdgeNativeReuse
open DaggerNativeInnerHornFactorization DaggerNativeJoyalMappingTest
open DaggerActualGeneralRightConeMapping DaggerActualRightMappingWeakInvariance
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerActualInnerConeIntervalComparison
noncomputable section

private abbrev canonicalProjection :=
  DaggerOriginalCounitRightConeContractibilityRetraction.projection.{u}

theorem simplex_quasicategory (n : ℕ) : (Δ[n] : SSet.{u}).Quasicategory := by
  have : (nerve (ULift.{u} (Fin (n + 1)))).Quasicategory := inferInstance
  exact DaggerNativeQuasicategoryOpposite.quasicategory_of_iso (SSet.stdSimplex.isoNerve n).symm

local instance intervalQuasicategory : (Δ[1] : SSet.{u}).Quasicategory :=
  simplex_quasicategory 1

def intervalRetraction : replacement.obj (Δ[1] : SSet.{u}) ⟶ Δ[1] :=
  (DaggerActualInnerReplacementExtensions.exists_retraction (Δ[1] : SSet.{u})).choose

theorem intervalRetraction_unit : unit.app (Δ[1] : SSet.{u}) ≫ intervalRetraction = 𝟙 _ :=
  (DaggerActualInnerReplacementExtensions.exists_retraction (Δ[1] : SSet.{u})).choose_spec

def extendedProjection (n : ℕ) : replacement.obj (cone.{u} n) ⟶ Δ[1] :=
  DaggerActualInnerReplacementExtensions.extension intervalRetraction (canonicalProjection n)

theorem unit_extendedProjection (n : ℕ) :
    unit.app (cone.{u} n) ≫ extendedProjection n = canonicalProjection n :=
  DaggerActualInnerReplacementExtensions.unit_extension intervalRetraction
    intervalRetraction_unit (canonicalProjection n)

theorem extendedProjection_weak (n : ℕ) :
    weakCategoricalEquivalences (extendedProjection.{u} n) :=
  weakCategoricalEquivalences.of_precomp (unit.app (cone n)) (extendedProjection n)
    (DaggerNativeInnerJoyalMappingWeak.unit_weak (cone n))
    ((unit_extendedProjection n).symm ▸ native_projection_categorical_weak n)

theorem extendedProjection_naturality {m n : SimplexCategory} (α : m ⟶ n) :
    replacement.map (coneMap.{u} α) ≫ extendedProjection n.len = extendedProjection m.len := by
  change replacement.map (coneMap α) ≫
    DaggerActualInnerReplacementExtensions.extension intervalRetraction
      (canonicalProjection n.len) = _
  rw [DaggerActualInnerReplacementExtensions.extension_naturality, native_projection_naturality]
  rfl

def zeroVertex : (Δ[1] : SSet.{u}).obj (op ⦋0⦌) :=
  SSet.stdSimplex.obj₀Equiv.symm (0 : Fin 2)

def oneVertex : (Δ[1] : SSet.{u}).obj (op ⦋0⦌) :=
  SSet.stdSimplex.obj₀Equiv.symm (1 : Fin 2)

def sourceAlpha (n : ℕ) : (replacement.obj (cone.{u} n)).obj (op ⦋0⦌) :=
  (unit.app (cone n)).app (op ⦋0⦌) (alpha n)

def sourceOmega (n : ℕ) : (replacement.obj (cone.{u} n)).obj (op ⦋0⦌) :=
  (unit.app (cone n)).app (op ⦋0⦌) (omega n)

theorem projection_alpha_value (n : ℕ) :
    (canonicalProjection.{u} n).app (op ⦋0⦌) (alpha n) = zeroVertex := by
  have h := congrFun (NatTrans.congr_app (alpha_projection.{u} n) (op ⦋0⦌))
    (SSet.stdSimplex.obj₀Equiv.symm (0 : Fin 1))
  simpa only [projection_eq_native] using h

theorem projection_omega_value (n : ℕ) :
    (canonicalProjection.{u} n).app (op ⦋0⦌) (omega n) = oneVertex := by
  have h := congrFun (NatTrans.congr_app (omega_projection.{u} n) (op ⦋0⦌))
    (SSet.stdSimplex.obj₀Equiv.symm (0 : Fin 1))
  simpa only [projection_eq_native] using h

theorem extendedProjection_alpha (n : ℕ) :
    (extendedProjection.{u} n).app (op ⦋0⦌) (sourceAlpha n) = zeroVertex :=
  (congrFun (NatTrans.congr_app (unit_extendedProjection n) (op ⦋0⦌)) (alpha n)).trans
    (projection_alpha_value n)

theorem extendedProjection_omega (n : ℕ) :
    (extendedProjection.{u} n).app (op ⦋0⦌) (sourceOmega n) = oneVertex :=
  (congrFun (NatTrans.congr_app (unit_extendedProjection n) (op ⦋0⦌)) (omega n)).trans
    (projection_omega_value n)

def mappingComparison (n : ℕ) :
    rightMapping (replacement.obj (cone.{u} n)) (sourceAlpha n) (sourceOmega n) ⟶
      rightMapping (Δ[1] : SSet.{u}) zeroVertex oneVertex :=
  mapTo (extendedProjection n) (sourceAlpha n) (sourceOmega n)
    zeroVertex oneVertex (extendedProjection_alpha n) (extendedProjection_omega n)

theorem mappingComparison_weak (n : ℕ) : WeakEquivalence (mappingComparison.{u} n) := by
  have h : ∀ (c d : (Δ[1] : SSet.{u}).obj (op ⦋0⦌))
      (hc : (extendedProjection n).app (op ⦋0⦌) (sourceAlpha n) = c)
      (hd : (extendedProjection n).app (op ⦋0⦌) (sourceOmega n) = d),
      WeakEquivalence (mapTo (extendedProjection n) (sourceAlpha n) (sourceOmega n) c d hc hd) := by
    intro c d hc hd
    subst c
    subst d
    exact map_weak_of_categorical_weak (extendedProjection n) (extendedProjection_weak n)
      (sourceAlpha n) (sourceOmega n)
  exact h zeroVertex oneVertex (extendedProjection_alpha n) (extendedProjection_omega n)

end
end DaggerActualInnerConeIntervalComparison
