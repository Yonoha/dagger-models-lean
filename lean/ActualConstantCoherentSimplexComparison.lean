import ActualConstantPathEvaluation

/-! Coherent simplices in every actual constant enrichment are exactly ordinary simplices. -/
set_option autoImplicit false
open CategoryTheory Opposite Simplicial DaggerModels OrdinaryRigidification
open DaggerActualConstantSimplicialCategory DaggerActualThickeningPathContractibility
open DaggerActualConstantPathEvaluation
open scoped Simplicial
universe u
namespace DaggerActualConstantCoherentSimplexComparison
noncomputable section
variable (A : Type u) [Category.{u} A]

local instance : EnrichedCategory SSet.{u} A := DaggerUnitaryDiscrete.ordinaryEnriched A

def toOrdinary (n : SimplexCategory) (F : cosimplicialThickening.obj n ⟶ constant A) :
    Fin (n.len + 1) ⥤ A where
  obj i := F.obj ⟨⟨i⟩⟩
  map {i j} f := (F.map ⟨⟨i⟩⟩ ⟨⟨j⟩⟩).app (op ⦋0⦌)
    (ComposableArrows.mk₀
      (shortestPath (⟨i⟩ : ULift.{u} (Fin (n.len + 1))) ⟨j⟩
        (show i ≤ j from leOfHom f)))
  map_id i := by
    have hh := congrFun
      (NatTrans.congr_app (F.map_id ⟨⟨i⟩⟩) (op ⦋0⦌)) PUnit.unit
    exact (map_eq_shortest (⟨i⟩ : ULift.{u} (Fin (n.len + 1))) ⟨i⟩ le_rfl
      (F.map ⟨⟨i⟩⟩ ⟨⟨i⟩⟩) _ _).symm.trans hh
  map_comp {i j k} f g := by
    let p := ComposableArrows.mk₀
      (shortestPath (⟨i⟩ : ULift.{u} (Fin (n.len + 1))) ⟨j⟩ (show i ≤ j from leOfHom f))
    let q := ComposableArrows.mk₀
      (shortestPath (⟨j⟩ : ULift.{u} (Fin (n.len + 1))) ⟨k⟩ (show j ≤ k from leOfHom g))
    have hh := congrFun
      (NatTrans.congr_app (F.map_comp ⟨⟨i⟩⟩ ⟨⟨j⟩⟩ ⟨⟨k⟩⟩) (op ⦋0⦌)) (p, q)
    exact (map_eq_shortest (⟨i⟩ : ULift.{u} (Fin (n.len + 1))) ⟨k⟩
      ((leOfHom f).trans (leOfHom g)) (F.map ⟨⟨i⟩⟩ ⟨⟨k⟩⟩) _ _).symm.trans hh

def fromOrdinary (n : SimplexCategory) (F : Fin (n.len + 1) ⥤ A) :
    cosimplicialThickening.obj n ⟶ constant A where
  obj i := F.obj i.as.down
  map i j :=
    { app := fun _ γ ↦ F.map (homOfLE (show i.as.down ≤ j.as.down from
        @SimplicialThickening.Path.le
          (ULift.{u} (Fin (n.len + 1))) _ i.as j.as (γ.obj 0)))
      naturality := by intros; rfl }
  map_id i := by
    ext q p
    exact F.map_id i.as.down
  map_comp i j k := by
    ext q p
    exact F.map_comp _ _

theorem to_from (n : SimplexCategory) (F : Fin (n.len + 1) ⥤ A) :
    toOrdinary A n (fromOrdinary A n F) = F := by
  refine CategoryTheory.Functor.hext (fun _ ↦ rfl) ?_
  intro x y f
  rfl

theorem from_to (n : SimplexCategory) (F : cosimplicialThickening.obj n ⟶ constant A) :
    fromOrdinary A n (toOrdinary A n F) = F := by
  apply EnrichedFunctor.ext SSet (fun i ↦ by cases i; rfl)
  intro i j
  simp only [eqToHom_refl, Category.comp_id]
  ext q γ
  exact (map_eq_shortest i.as j.as (SimplicialThickening.Path.le (γ.obj 0))
    (F.map i j) q γ).symm

end
end DaggerActualConstantCoherentSimplexComparison
