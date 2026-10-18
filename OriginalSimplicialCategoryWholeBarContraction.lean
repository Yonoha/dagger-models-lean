import OriginalSimplicialCategoryWholeBarContractionMap

/-!
# The actual original whole bar homotopy retains every endpoint component

The assembled cylinder starts at the actual identity and ends at the native
coproduct of the original terminal-chain endomorphisms. Each component keeps
its own original endpoint; the entire bar is not collapsed to a single point.
-/
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Opposite Simplicial DaggerModels
open scoped MonoidalCategory
open DaggerOriginalSimplicialCategoryBarConstruction
open DaggerOriginalSimplicialCategoryBarCoproductDegrees
open DaggerOriginalSimplicialCategoryBarContraction
open DaggerOriginalSimplicialCategoryWholeBarContractionMap
universe u
namespace DaggerOriginalSimplicialCategoryWholeBarContraction
noncomputable section

/-- The native coproduct of the original terminal-chain maps preserves all endpoints. -/
def wholeBarTerminalEnd (C : SimplicialCat.{u, u}) : bar C ⟶ bar C :=
  Limits.Sigma.map (terminalBarEnd C)

/-- The whole terminal endomorphism retains the actual component and its original map. -/
theorem wholeBarTerminalEnd_apply (C : SimplicialCat.{u, u}) (n : SimplexCategoryᵒᵖ)
    (y : C.Obj) (a : (barComponent C y).obj n) :
    (wholeBarTerminalEnd C).app n (barDegreeEquiv C n ⟨y, a⟩) =
      barDegreeEquiv C n ⟨y, (terminalBarEnd C y).app n a⟩ :=
  congrFun (NatTrans.congr_app (Sigma.ι_map (terminalBarEnd C) y) n) a

/-- The whole cylinder starts at the original whole bar identity. -/
theorem wholeBarContractionMap_zero (C : SimplicialCat.{u, u}) :
    SSet.ι₀ ≫ wholeBarContractionMap C = 𝟙 (bar C) := by
  apply NatTrans.ext
  funext n a
  obtain ⟨⟨y, a⟩, rfl⟩ := (barDegreeEquiv C n).surjective a
  change wholeBarCylinderDegree C n
      (barDegreeEquiv C n ⟨y, a⟩, ((SSet.ι₀ (X := barComponent C y)).app n a).2) =
    barDegreeEquiv C n ⟨y, a⟩
  rw [wholeBarCylinderDegree_apply]
  exact congrArg (fun b ↦ barDegreeEquiv C n ⟨y, b⟩)
    (congrFun (NatTrans.congr_app (barContractionMap_zero C y) n) a)

/-- The whole cylinder ends at the native coproduct of the original terminal-chain maps. -/
theorem wholeBarContractionMap_one (C : SimplicialCat.{u, u}) :
    SSet.ι₁ ≫ wholeBarContractionMap C = wholeBarTerminalEnd C := by
  apply NatTrans.ext
  funext n a
  obtain ⟨⟨y, a⟩, rfl⟩ := (barDegreeEquiv C n).surjective a
  change wholeBarCylinderDegree C n
      (barDegreeEquiv C n ⟨y, a⟩, ((SSet.ι₁ (X := barComponent C y)).app n a).2) =
    (wholeBarTerminalEnd C).app n (barDegreeEquiv C n ⟨y, a⟩)
  rw [wholeBarCylinderDegree_apply, wholeBarTerminalEnd_apply]
  exact congrArg (fun b ↦ barDegreeEquiv C n ⟨y, b⟩)
    (congrFun (NatTrans.congr_app (barContractionMap_one C y) n) a)

/-- The actual original whole bar homotopy preserves every original endpoint index. -/
def wholeBarHomotopy (C : SimplicialCat.{u, u}) :
    SSet.Homotopy (𝟙 (bar C)) (wholeBarTerminalEnd C) :=
  SSet.Homotopy.mk (wholeBarContractionMap C) (wholeBarContractionMap_zero C)
    (wholeBarContractionMap_one C)

end
end DaggerOriginalSimplicialCategoryWholeBarContraction
