import OriginalSimplicialCategoryBarFibreFunctor
import NerveHomotopy

/-!
# The original degreewise terminal objects and the coherent terminal transformation

Each over category has its original identity arrow as terminal object. The
original degree operators preserve this object and the entire canonical
natural transformation from identity to the constant terminal endofunctor.
The direction is identity-to-constant; no reversal of simplicial homotopies
or diagonal contraction is assumed here.
-/
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Opposite Simplicial DaggerModels
open DaggerOriginalSimplicialDegreeCategory
open DaggerOriginalSimplicialCategoryOverDiagram
open DaggerOriginalSimplicialCategoryBarFunctor
universe u
namespace DaggerOriginalSimplicialCategoryBarTerminal
noncomputable section

/-- The exact original degreewise identity arrow, as a native over object. -/
def terminalOverObject (C : SimplicialCat.{u, u}) (y : C.Obj) (n : SimplexCategoryᵒᵖ) :
    overObjects C y n :=
  Over.mk (T := degreeObjects C n)
    (@CategoryStruct.id (degreeObjects C n) (degreeCategory C n).toCategoryStruct y)

/-- The entire over-category endofunctor constant at the original identity arrow. -/
def terminalOverEndofunctor (C : SimplicialCat.{u, u}) (y : C.Obj)
    (n : SimplexCategoryᵒᵖ) : overObjects C y n ⥤ overObjects C y n :=
  (Functor.const (overObjects C y n)).obj (terminalOverObject C y n)

/-- Every original over object has its terminal arrow, naturally on all triangles. -/
def terminalOverNatTrans (C : SimplicialCat.{u, u}) (y : C.Obj)
    (n : SimplexCategoryᵒᵖ) : 𝟭 (overObjects C y n) ⟶ terminalOverEndofunctor C y n where
  app a := (overDegreeTerminal C y n).from a
  naturality _ _ _ := (overDegreeTerminal C y n).hom_ext _ _

/-- The canonical terminal arrow is exactly the original final arrow on underlying maps. -/
theorem terminalOverNatTrans_app_left (C : SimplicialCat.{u, u}) (y : C.Obj)
    (n : SimplexCategoryᵒᵖ) (a : overObjects C y n) :
    ((terminalOverNatTrans C y n).app a).left = a.hom := by
  have h := Over.w ((terminalOverNatTrans C y n).app a)
  simpa [terminalOverEndofunctor, terminalOverObject] using h

/-- Every original simplicial operator preserves the same original terminal identity. -/
theorem terminalOverObject_map (C : SimplicialCat.{u, u}) (y : C.Obj)
    {n m : SimplexCategoryᵒᵖ} (i : n ⟶ m) :
    (overDegreeMap C y i).obj (terminalOverObject C y n) = terminalOverObject C y m := by
  apply DaggerOriginalOverNerveFibreChallengeProof.overObject_eq
    (a := (overDegreeMap C y i).obj (terminalOverObject C y n))
    (b := terminalOverObject C y m) rfl
  exact heq_of_eq ((degreeMap C i).map_id y)

/-- The whole terminal transformation is coherent under every original degree operator. -/
theorem terminalOverNatTrans_map (C : SimplicialCat.{u, u}) (y : C.Obj)
    {n m : SimplexCategoryᵒᵖ} (i : n ⟶ m) (a : overObjects C y n) :
    HEq ((overDegreeMap C y i).map ((terminalOverNatTrans C y n).app a))
      ((terminalOverNatTrans C y m).app ((overDegreeMap C y i).obj a)) := by
  apply DaggerOriginalSimplicialCategoryOverDiagram.overHom_heq rfl
    (terminalOverObject_map C y i)
  apply heq_of_eq
  change (degreeMap C i).map ((terminalOverNatTrans C y n).app a).left =
    ((terminalOverNatTrans C y m).app ((overDegreeMap C y i).obj a)).left
  rw [terminalOverNatTrans_app_left, terminalOverNatTrans_app_left]
  rfl

/-- The original whole enriched functor preserves the terminal identity in every degree. -/
theorem terminalOverObject_functor {C D : SimplicialCat.{u, u}} (F : C ⟶ D)
    (y : C.Obj) (n : SimplexCategoryᵒᵖ) :
    (overDegreeFunctor F y n).obj (terminalOverObject C y n) =
      terminalOverObject D (F.obj y) n := by
  apply DaggerOriginalOverNerveFibreChallengeProof.overObject_eq
    (a := (overDegreeFunctor F y n).obj (terminalOverObject C y n))
    (b := terminalOverObject D (F.obj y) n) rfl
  exact heq_of_eq ((degreeFunctor F n).map_id y)

end
end DaggerOriginalSimplicialCategoryBarTerminal
