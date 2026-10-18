import OriginalSimplicialCategoryBarTerminalAction

/-!
# The coherent original diagonal bar cylinder

The native nerve cylinder of the terminal natural transformation commutes
with every original degree operator. Its diagonal therefore gives a cylinder
map on the original bar component, without replacing the component or its maps.
-/
set_option autoImplicit false
open CategoryTheory Opposite Simplicial DaggerModels
open scoped MonoidalCategory
open DaggerOriginalSimplicialDegreeCategory
open DaggerOriginalSimplicialCategoryOverDiagram
open DaggerOriginalSimplicialCategoryBarConstruction
open DaggerOriginalSimplicialCategoryBarTerminal
open DaggerOriginalSimplicialCategoryBarTerminalAction
universe u
namespace DaggerOriginalSimplicialCategoryBarContractionMap
noncomputable section

/-- The entire native nerve cylinder is natural in the original degree operator. -/
theorem terminalNerveCylinder_natural (C : SimplicialCat.{u, u}) (y : C.Obj)
    {n m : SimplexCategoryᵒᵖ} (i : n ⟶ m) :
    (nerveMap (overDegreeMap C y i) ⊗ₘ 𝟙 Δ[1]) ≫
        DaggerNerveHomotopy.natTransMap (terminalOverNatTrans C y m) =
      DaggerNerveHomotopy.natTransMap (terminalOverNatTrans C y n) ≫
        nerveMap (overDegreeMap C y i) := by
  apply NatTrans.ext
  funext k p
  change ((SimplexCategory.toCat.map (SSet.stdSimplex.objEquiv p.2)).toFunctor.prod'
      (p.1 ⋙ overDegreeMap C y i)) ⋙ terminalAction C y m =
    ((SimplexCategory.toCat.map (SSet.stdSimplex.objEquiv p.2)).toFunctor.prod' p.1 ⋙
      terminalAction C y n) ⋙ overDegreeMap C y i
  let A := (SimplexCategory.toCat.map (SSet.stdSimplex.objEquiv p.2)).toFunctor.prod' p.1
  change A ⋙ (𝟭 (Fin 2)).prod (overDegreeMap C y i) ⋙ terminalAction C y m =
    (A ⋙ terminalAction C y n) ⋙ overDegreeMap C y i
  rw [terminalAction_map]
  rfl

/-- The original degreewise terminal cylinders assemble on the full original diagonal. -/
def barContractionMap (C : SimplicialCat.{u, u}) (y : C.Obj) :
    barComponent C y ⊗ Δ[1] ⟶ barComponent C y where
  app n := (DaggerNerveHomotopy.natTransMap (terminalOverNatTrans C y n)).app n
  naturality n m i := by
    funext p
    have hh := congrFun ((DaggerNerveHomotopy.natTransMap
      (terminalOverNatTrans C y m)).naturality i)
      ((nerveMap (overDegreeMap C y i)).app n p.1, p.2)
    have hv := congrFun (NatTrans.congr_app (terminalNerveCylinder_natural C y i) n) p
    change (DaggerNerveHomotopy.natTransMap (terminalOverNatTrans C y m)).app m
        ((nerve (overObjects C y m)).map i
          ((nerveMap (overDegreeMap C y i)).app n p.1), Δ[1].map i p.2) =
      (nerve (overObjects C y m)).map i
        ((nerveMap (overDegreeMap C y i)).app n
          ((DaggerNerveHomotopy.natTransMap (terminalOverNatTrans C y n)).app n p))
    exact hh.trans (congrArg ((nerve (overObjects C y m)).map i) hv)

end
end DaggerOriginalSimplicialCategoryBarContractionMap
