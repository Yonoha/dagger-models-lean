import ActualDaggerIsomorphismComponentFactor
import ActualRigidifiedDaggerCoreCompletion

/-! The actual original rigidified core inclusion lands in ALL isomorphism components. -/
set_option autoImplicit false
open CategoryTheory Opposite Simplicial DaggerModels OrdinaryRigidification
open DaggerActualDaggerOrdinaryCore DaggerActualDaggerIsomorphismComponentFactor
universe u
namespace DaggerActualDaggerCoreIsomorphismComponentComparison
noncomputable section

def comparison (X : DaggerSSet.{u}) [X.toSSet.Quasicategory] :
    DaggerRigidification.obj (coreDagger X) ⟶
      DaggerActualDaggerIsomorphismComponentPart.part (DaggerRigidification.obj X) := by
  letI := coreDagger_kan X
  exact factor (DaggerRigidification.map (DaggerActualDaggerOrdinaryCoreMaps.inclusion X))
    (DaggerActualKanRigidificationCompletionWeak.component_groupoid (coreDagger X).toSSet)

theorem comparison_comp_inclusion (X : DaggerSSet.{u}) [X.toSSet.Quasicategory] :
    comparison X ≫
        DaggerActualDaggerIsomorphismComponentPart.inclusion (DaggerRigidification.obj X) =
      DaggerRigidification.map (DaggerActualDaggerOrdinaryCoreMaps.inclusion X) := by
  letI := coreDagger_kan X
  exact factor_comp_inclusion _ _

theorem comparison_obj (X : DaggerSSet.{u}) [X.toSSet.Quasicategory]
    (x : (DaggerRigidification.obj (coreDagger X)).Obj) :
    (comparison X).obj x =
      (DaggerRigidification.map (DaggerActualDaggerOrdinaryCoreMaps.inclusion X)).obj x :=
  rfl

theorem comparison_map_val (X : DaggerSSet.{u}) [X.toSSet.Quasicategory]
    (x y : (DaggerRigidification.obj (coreDagger X)).Obj) (q : SimplexCategoryᵒᵖ)
    (s : ((DaggerRigidification.obj (coreDagger X)).enriched.Hom x y).obj q) :
    ((comparison X).map x y |>.app q s).val =
      ((DaggerRigidification.map (DaggerActualDaggerOrdinaryCoreMaps.inclusion X)).map x y).app
        q s :=
  rfl

end
end DaggerActualDaggerCoreIsomorphismComponentComparison
