import OriginalSimplicialCategoryBarContractionMap

/-!
# The original bar component contracts toward its original identity vertex

Construct an actual simplicial homotopy from the identity of the full original
bar component to the constant map at its original identity-arrow vertex.
This directed simplicial homotopy is not reversed in simplicial sets.
-/
set_option autoImplicit false
open CategoryTheory Opposite Simplicial DaggerModels
open scoped MonoidalCategory
open DaggerOriginalSimplicialDegreeCategory
open DaggerOriginalSimplicialCategoryOverDiagram
open DaggerOriginalSimplicialCategoryBarConstruction
open DaggerOriginalSimplicialCategoryBarTerminal
open DaggerOriginalSimplicialCategoryBarContractionMap
universe u
namespace DaggerOriginalSimplicialCategoryBarContraction
noncomputable section

/-- The original constant chain at the original terminal identity arrow in every degree. -/
def terminalSimplex (C : SimplicialCat.{u, u}) (y : C.Obj) (n : SimplexCategoryᵒᵖ) :
    (barComponent C y).obj n :=
  (Functor.const (Fin (n.unop.len + 1))).obj (terminalOverObject C y n)

/-- Every original simplicial operator preserves the same terminal constant chain. -/
theorem terminalSimplex_map (C : SimplicialCat.{u, u}) (y : C.Obj)
    {n m : SimplexCategoryᵒᵖ} (i : n ⟶ m) :
    (barComponent C y).map i (terminalSimplex C y n) = terminalSimplex C y m := by
  refine Functor.hext
    (F := (barComponent C y).map i (terminalSimplex C y n))
    (G := terminalSimplex C y m) (fun _ ↦ terminalOverObject_map C y i) ?_
  intro k l f
  apply DaggerOriginalSimplicialCategoryOverDiagram.overHom_heq
    (terminalOverObject_map C y i) (terminalOverObject_map C y i)
  exact heq_of_eq ((degreeMap C i).map_id y)

/-- The same original terminal vertex of the original bar component. -/
def terminalBarPoint (C : SimplicialCat.{u, u}) (y : C.Obj) :
    (barComponent C y).obj (op ⦋0⦌) := terminalSimplex C y (op ⦋0⦌)

/-- The end of the cylinder is the whole original terminal constant chain map. -/
def terminalBarEnd (C : SimplicialCat.{u, u}) (y : C.Obj) :
    barComponent C y ⟶ barComponent C y where
  app n _ := terminalSimplex C y n
  naturality _ _ i := by
    funext a
    exact (terminalSimplex_map C y i).symm

/-- The zero end of the original diagonal cylinder is the original identity map. -/
theorem barContractionMap_zero (C : SimplicialCat.{u, u}) (y : C.Obj) :
    SSet.ι₀ ≫ barContractionMap C y = 𝟙 (barComponent C y) := by
  apply NatTrans.ext
  funext n a
  have h := congrFun (NatTrans.congr_app
    (DaggerNerveHomotopy.natTransMap_zero (terminalOverNatTrans C y n)) n) a
  simpa [nerveMap] using h

/-- The one end of the original diagonal cylinder is its terminal constant chain map. -/
theorem barContractionMap_one (C : SimplicialCat.{u, u}) (y : C.Obj) :
    SSet.ι₁ ≫ barContractionMap C y = terminalBarEnd C y := by
  apply NatTrans.ext
  funext n a
  have h := congrFun (NatTrans.congr_app
    (DaggerNerveHomotopy.natTransMap_one (terminalOverNatTrans C y n)) n) a
  simpa [nerveMap, terminalOverEndofunctor, terminalSimplex, terminalBarEnd] using h

/-- The original terminal chain endomorphism is the native constant vertex map. -/
theorem terminalBarEnd_eq_const (C : SimplicialCat.{u, u}) (y : C.Obj) :
    terminalBarEnd C y = SSet.const (terminalBarPoint C y) := by
  apply NatTrans.ext
  funext n a
  exact (terminalSimplex_map C y (n.unop.const ⦋0⦌ 0).op).symm

/-- The actual whole original bar component has an identity-to-constant homotopy. -/
def barContraction (C : SimplicialCat.{u, u}) (y : C.Obj) :
    SSet.Homotopy (𝟙 (barComponent C y)) (SSet.const (terminalBarPoint C y)) :=
  SSet.Homotopy.mk (barContractionMap C y) (barContractionMap_zero C y)
    ((barContractionMap_one C y).trans (terminalBarEnd_eq_const C y))

end
end DaggerOriginalSimplicialCategoryBarContraction
