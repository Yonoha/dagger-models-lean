import OriginalFixedObjectGroupoidCompletionAdjunction
import OriginalFixedObjectGroupoidClasses
import DaggerModels.OrdinaryTwoObjectCell

/-!
# Reuse of the original ordinary two-object cell with fixed objects

Keep the original lifted Boolean object type and the original enrichment. Restrict
the proved full ordinary two-object cell universal property to identity-object maps.
Compose with the actual groupoid completion adjunction. No free groupoid, path
quotient or simplicial category laws are reimplemented.
-/
set_option autoImplicit false
open CategoryTheory DaggerModels
open DaggerOriginalFixedObjectSimplicialCategories
open DaggerOriginalFixedObjectGroupoidCompletionAdjunction
universe u
namespace DaggerOriginalFixedObjectOrdinaryCellAdjunction
noncomputable section

/-- The exact original two vertices, called left and right in the original cell. -/
abbrev TwoObjects := TwoObjectDaggerGraph.Vertex.{u}

/-- Recover a fixed-object map by eliminating precisely its identity object-function equality. -/
def fixedHomOfOriginal {O : Type u} {C D : FixedSimplicialCategory O}
    (F : original O C ⟶ original O D) (hF : F.obj = id) : C ⟶ D := by
  rcases F with ⟨obj, map, map_id, map_comp⟩
  cases hF
  exact ⟨map, map_id, map_comp⟩

/-- The full original functor is recovered; every Hom map and law is retained. -/
theorem originalHom_fixedHomOfOriginal {O : Type u} {C D : FixedSimplicialCategory O}
    (F : original O C ⟶ original O D) (hF : F.obj = id) :
    originalHom (fixedHomOfOriginal F hF) = F := by
  rcases F with ⟨obj, map, map_id, map_comp⟩
  cases hF
  rfl

/-- The original ordinary cell with the same fixed two vertices and full enrichment. -/
def cell (K : SSet.{u}) : FixedSimplicialCategory TwoObjects :=
  ⟨OrdinaryTwoObjectCell.enriched K⟩

/-- The full original cell map fixes the original left and right vertices. -/
def cellMap {K L : SSet.{u}} (f : K ⟶ L) : cell K ⟶ cell L :=
  fixedHomOfOriginal (OrdinaryTwoObjectCell.map f) (by
    funext x
    rcases x with ⟨b⟩
    cases b <;> rfl)

/-- Recover exactly the original parameter map, including its full enriched functor. -/
theorem originalHom_cellMap {K L : SSet.{u}} (f : K ⟶ L) :
    originalHom (cellMap f) = OrdinaryTwoObjectCell.map f :=
  originalHom_fixedHomOfOriginal _ _

/-- The parameter functor is the existing ordinary cell functor on all Hom maps. -/
def cellFunctor : SSet.{u} ⥤ FixedSimplicialCategory TwoObjects where
  obj := cell
  map := cellMap
  map_id K := by
    apply originalHom_injective
    rw [originalHom_cellMap]
    exact OrdinaryTwoObjectCell.functor.map_id K
  map_comp f g := by
    apply originalHom_injective
    change originalHom (cellMap (f ≫ g)) =
      originalHom (cellMap f) ≫ originalHom (cellMap g)
    rw [originalHom_cellMap, originalHom_cellMap, originalHom_cellMap]
    exact OrdinaryTwoObjectCell.functor.map_comp f g

/-- Original evaluation at the exact left-to-right Hom. -/
def evaluation : FixedSimplicialCategory TwoObjects ⥤ SSet.{u} :=
  DaggerOriginalFixedObjectGroupoidClasses.homEvaluation
    TwoObjects TwoObjectDaggerGraph.left TwoObjectDaggerGraph.right

/-- The existing original classified functor fixes both vertices, hence the whole object type. -/
theorem fromData_obj (K : SSet.{u}) (C : FixedSimplicialCategory TwoObjects)
    (f : K ⟶ (evaluation.obj C)) :
    (OrdinaryTwoObjectCell.fromData K (original TwoObjects C)
      TwoObjectDaggerGraph.left TwoObjectDaggerGraph.right f).obj = id := by
  funext x
  rcases x with ⟨b⟩
  cases b <;> rfl

/-- Restrict the original classified functor, retaining the same generator Hom map. -/
def fromData (K : SSet.{u}) (C : FixedSimplicialCategory TwoObjects)
    (f : K ⟶ evaluation.obj C) : cell K ⟶ C :=
  fixedHomOfOriginal (OrdinaryTwoObjectCell.fromData K (original TwoObjects C)
    TwoObjectDaggerGraph.left TwoObjectDaggerGraph.right f) (fromData_obj K C f)

/-- The restriction retains the same full original classified functor. -/
theorem originalHom_fromData (K : SSet.{u}) (C : FixedSimplicialCategory TwoObjects)
    (f : K ⟶ evaluation.obj C) :
    originalHom (fromData K C f) = OrdinaryTwoObjectCell.fromData K (original TwoObjects C)
      TwoObjectDaggerGraph.left TwoObjectDaggerGraph.right f :=
  originalHom_fixedHomOfOriginal _ _

/-- The full fixed-object universal property is inherited from the original cell. -/
def homEquiv (K : SSet.{u}) (C : FixedSimplicialCategory TwoObjects) :
    (cell K ⟶ C) ≃ (K ⟶ evaluation.obj C) where
  toFun F := F.map TwoObjectDaggerGraph.left TwoObjectDaggerGraph.right
  invFun := fromData K C
  left_inv F := by
    apply originalHom_injective
    rw [originalHom_fromData]
    exact OrdinaryTwoObjectCell.fromData_classify (originalHom F)
  right_inv f := by
    have he := DaggerOriginalStrictGroupoidObjectFixedC2Actions.enrichedFunctor_map_heq
      (originalHom_fromData K C f) TwoObjectDaggerGraph.left TwoObjectDaggerGraph.right
    exact (eq_of_heq he).trans (OrdinaryTwoObjectCell.fromData_map_left_right K
      (original TwoObjects C) TwoObjectDaggerGraph.left TwoObjectDaggerGraph.right f)

/-- The existing ordinary cell is left adjoint to the exact fixed left-to-right evaluation. -/
def cellAdjunction : cellFunctor.{u} ⊣ evaluation :=
  Adjunction.mkOfHomEquiv
    { homEquiv := homEquiv
      homEquiv_naturality_left_symm := by
        intro K L C f g
        apply originalHom_injective
        change originalHom (fromData K C (f ≫ g)) =
          originalHom (cellMap f) ≫ originalHom (fromData L C g)
        rw [originalHom_fromData, originalHom_cellMap, originalHom_fromData]
        exact OrdinaryTwoObjectCell.fromData_naturality_left (original TwoObjects C) f
          TwoObjectDaggerGraph.left TwoObjectDaggerGraph.right g
      homEquiv_naturality_right := by
        intro K C D F G
        rfl }

/-- Actual ordinary free groupoid on the original two-object cell generators. -/
def freeGroupoid : SSet.{u} ⥤ FixedStrictGroupoids TwoObjects :=
  cellFunctor ⋙ fixedCompletion TwoObjects

/-- The original strict groupoid Hom evaluation retains both exact fixed vertices. -/
def strictEvaluation : FixedStrictGroupoids TwoObjects ⥤ SSet.{u} :=
  fixedInclusion TwoObjects ⋙ evaluation

/-- Ordinary free groupoid and original Hom evaluation are adjoint by the actual completions. -/
def freeGroupoidAdjunction : freeGroupoid.{u} ⊣ strictEvaluation :=
  cellAdjunction.comp (fixedCompletionInclusionAdjunction TwoObjects)

end
end DaggerOriginalFixedObjectOrdinaryCellAdjunction
