import ActualIteratedGadgetData
import ActualFibrantOrdinalPropagation

/-! Every level of the small gadget family retains actual endpoint contractibility. -/

set_option autoImplicit false
open CategoryTheory Opposite Simplicial HomotopicalAlgebra
open MonoidalCategory CartesianMonoidalCategory DaggerModels OrdinaryRigidification
open DaggerActualFibrantGadgetData DaggerActualIteratedGadgetData
open DaggerActualFibrantOrdinalPropagation DaggerChosenRigidificationNecklace
open scoped Simplicial SSet.modelCategoryQuillen
universe u

namespace DaggerActualIteratedGadgetProperties
noncomputable section

def dimension (P : BaseCode) : ℕ := match P with
  | Sum.inl T => T.len
  | Sum.inr _ => 1

/-- Actual ordinal comparison data are constructed at every level, including the original level. -/
theorem has_comparison (P : BaseCode) (k : ℕ) :
    hasOrdinalComparison (spaceAt.{u} P k) (dimension P) := by
  induction k with
  | zero =>
    cases P with
    | inl T =>
      exact ⟨DaggerActualNecklaceOrdinalComparison.comparison T,
        DaggerActualNecklaceOrdinalComparison.comparison_surjective T,
        DaggerActualNecklaceOrdinalComparison.comparison_hom_GW T⟩
    | inr n =>
      exact ⟨DaggerActualFibrantRightConeContractibility.comparison n,
        DaggerActualFibrantRightConeContractibility.comparison_surjective n,
        DaggerActualFibrantRightConeContractibility.comparison_hom_GW n⟩
  | succ k ih => exact next ih

/-- The native C of every level has weakly contractible nonempty Homs. -/
theorem nonempty_hom_GW (P : BaseCode) (k : ℕ)
    (a b : (rigidification.obj (spaceAt.{u} P k)).Obj)
    (h : Nonempty ((a ⟶[SSet.{u}] b).obj (op ⦋0⦌))) :
    DaggerSSetGluing.GW (toUnit (a ⟶[SSet.{u}] b)) :=
  hom_toUnit_GW (has_comparison P k) a b h

/-- A concrete vertex in the actual endpoint Hom is carried through each literal unit. -/
theorem endpoint_nonempty (P : BaseCode) (k : ℕ) :
    Nonempty ((RV (spaceAt.{u} P k) (alphaAt P k) ⟶[SSet.{u}]
      RV (spaceAt P k) (omegaAt P k)).obj (op ⦋0⦌)) := by
  induction k with
  | zero =>
    cases P with
    | inl T => exact ⟨DaggerActualFibrantNecklaceContractibility.endpoint_vertex T⟩
    | inr n => exact ⟨DaggerActualFibrantRightConeEndpoints.endpoint_vertex n⟩
  | succ k ih =>
    obtain ⟨v⟩ := ih
    let f := rigidification.map (DaggerActualFibrantGadgetData.unit.app (spaceAt P k))
    have ha : f.obj (RV (spaceAt P k) (alphaAt P k)) =
        RV (spaceAt P (k + 1)) (alphaAt P (k + 1)) :=
      RigidificationVertices.vertexEquiv_naturality _ _
    have hb : f.obj (RV (spaceAt P k) (omegaAt P k)) =
        RV (spaceAt P (k + 1)) (omegaAt P (k + 1)) :=
      RigidificationVertices.vertexEquiv_naturality _ _
    exact ⟨(f.map (RV (spaceAt P k) (alphaAt P k)) (RV (spaceAt P k) (omegaAt P k)) ≫
      targetHomTransport ha hb).app (op ⦋0⦌) v⟩

/-- Every original endpoint pair in this small family has weakly contractible native C Hom. -/
theorem endpoint_hom_GW (P : Code) :
    DaggerSSetGluing.GW (toUnit (RV (space.{u} P) (alpha P) ⟶[SSet.{u}]
      RV (space P) (omega P))) :=
  nonempty_hom_GW P.base P.level _ _ (endpoint_nonempty P.base P.level)

/-- Every positive level is an actual coherent nerve of a locally Kan replacement. -/
theorem positive_quasicategory (P : Code) (h : 0 < P.level) :
    SSet.Quasicategory (space.{u} P) := by
  cases P with
  | mk P k =>
    cases k with
    | zero => exact False.elim (Nat.not_lt_zero _ h)
    | succ k => exact DaggerActualFibrantGadgetExtensions.gadget_quasicategory (spaceAt P k)

end
end DaggerActualIteratedGadgetProperties
