import OriginalSimplicialCategoryBarTerminal

/-!
# The whole original terminal cylinder action

Uncurry the native one-arrow diagram of the original terminal transformation.
Its action on the product with the walking arrow is coherent with every
original degree operator, retaining the original identity and final arrows.
This is the vertical coherence needed for the original diagonal bar homotopy.
-/
set_option autoImplicit false
open CategoryTheory Opposite Simplicial DaggerModels
open DaggerOriginalSimplicialDegreeCategory
open DaggerOriginalSimplicialCategoryOverDiagram
open DaggerOriginalSimplicialCategoryBarTerminal
universe u
namespace DaggerOriginalSimplicialCategoryBarTerminalAction
noncomputable section

/-- The native walking-arrow action of the whole original terminal transformation. -/
def terminalAction (C : SimplicialCat.{u, u}) (y : C.Obj) (n : SimplexCategoryᵒᵖ) :
    Fin 2 × overObjects C y n ⥤ overObjects C y n :=
  Functor.uncurry.obj (ComposableArrows.mk₁ (terminalOverNatTrans C y n))

/-- The whole terminal cylinder action commutes with every original degree operator. -/
theorem terminalAction_map (C : SimplicialCat.{u, u}) (y : C.Obj)
    {n m : SimplexCategoryᵒᵖ} (i : n ⟶ m) :
    (𝟭 (Fin 2)).prod (overDegreeMap C y i) ⋙ terminalAction C y m =
      terminalAction C y n ⋙ overDegreeMap C y i := by
  have hobj : ∀ p, ((𝟭 (Fin 2)).prod (overDegreeMap C y i) ⋙
      terminalAction C y m).obj p =
        (terminalAction C y n ⋙ overDegreeMap C y i).obj p := by
    rintro ⟨k, a⟩
    fin_cases k
    · rfl
    · exact (terminalOverObject_map C y i).symm
  refine Functor.hext hobj ?_
  rintro ⟨k, a⟩ ⟨l, b⟩ e
  apply DaggerOriginalSimplicialCategoryOverDiagram.overHom_heq (hobj _) (hobj _)
  fin_cases k <;> fin_cases l
  · simp [terminalAction, Functor.uncurry, ComposableArrows.mk₁,
      ComposableArrows.Mk₁.obj, ComposableArrows.Mk₁.map]
  · simp [terminalAction, Functor.uncurry, ComposableArrows.mk₁,
      ComposableArrows.Mk₁.obj, ComposableArrows.Mk₁.map, terminalOverEndofunctor,
      terminalOverNatTrans_app_left, overDegreeMap, Over.post]
  · have ht : (1 : Fin 2) ≤ 0 := leOfHom e.1
    norm_num at ht
  · simp [terminalAction, Functor.uncurry, ComposableArrows.mk₁,
      ComposableArrows.Mk₁.obj, ComposableArrows.Mk₁.map, terminalOverEndofunctor]
    rfl

end
end DaggerOriginalSimplicialCategoryBarTerminalAction
