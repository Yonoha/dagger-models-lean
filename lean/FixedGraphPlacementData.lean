import FixedGraphPlacements

/-! Exact active/inactive fibers and maps of the original-graph placements. -/

open CategoryTheory Limits DaggerModels DaggerFixedGraph DaggerPlacementStructure
open DaggerFixedGraphPlacements

universe u

namespace DaggerFixedGraphPlacementData

noncomputable section

variable {O : Type u}
local instance : LinearOrder O := chosenLinearOrder O
attribute [local instance] Classical.propDecidable

/-- These are the full original Ψ parameters; all inactive coordinates are retained. -/
def upperActionParameters (p : UpperIndex O) (K : SSet.{u}) : Parameters O :=
  (singleObj p K, fun _ ↦
    (Action.functorCategoryEquivalence SSet.{u} C2).inverse.obj
      (⊥_ (DaggerFreeBC2.BC2 ⥤ SSet.{u})))

def diagonalActionParameters (x : O) (K : SSet.{u}) : Parameters O :=
  (emptyUpper O, fun y ↦ (Action.functorCategoryEquivalence SSet.{u} C2).inverse.obj
    (singleObj x (DaggerFreeBC2.free.obj K) y))

def upperActionMap (p : UpperIndex O) {K L : SSet.{u}} (f : K ⟶ L) :
    upperActionParameters p K ⟶ upperActionParameters p L :=
  (singleMap p f, fun _ ↦ 𝟙 _)

def diagonalActionMap (x : O) {K L : SSet.{u}} (f : K ⟶ L) :
    diagonalActionParameters x K ⟶ diagonalActionParameters x L :=
  (fun _ ↦ 𝟙 _, fun y ↦ (Action.functorCategoryEquivalence SSet.{u} C2).inverse.map
    (singleMap x (DaggerFreeBC2.free.map f) y))

theorem upper_reconstruction (p : UpperIndex O) (K : SSet.{u}) :
    (upperPlacement O p).obj K = inverseObj (upperActionParameters p K) := rfl

theorem diagonal_reconstruction (x : O) (K : SSet.{u}) :
    (diagonalPlacement O x).obj K = inverseObj (diagonalActionParameters x K) := rfl

theorem upper_active (p : UpperIndex O) (K : SSet.{u}) :
    ((upperPlacement O p).obj K).Hom p.val.1 p.val.2 = K := by
  simp [upper_reconstruction, inverseObj, inverseHom, upperActionParameters,
    singleObj, p.property]

theorem upper_reverse_active (p : UpperIndex O) (K : SSet.{u}) :
    ((upperPlacement O p).obj K).Hom p.val.2 p.val.1 = K := by
  simp [upper_reconstruction, inverseObj, inverseHom, upperActionParameters,
    singleObj, p.property, not_lt_of_gt p.property]

theorem upper_inactive (p q : UpperIndex O) (h : q ≠ p) (K : SSet.{u}) :
    ((upperPlacement O p).obj K).Hom q.val.1 q.val.2 = ⊥_ SSet.{u} := by
  simp [upper_reconstruction, inverseObj, inverseHom, upperActionParameters,
    singleObj, q.property, h]

theorem upper_reverse_inactive (p q : UpperIndex O) (h : q ≠ p) (K : SSet.{u}) :
    ((upperPlacement O p).obj K).Hom q.val.2 q.val.1 = ⊥_ SSet.{u} := by
  simp [upper_reconstruction, inverseObj, inverseHom, upperActionParameters,
    singleObj, q.property, not_lt_of_gt q.property, h]

theorem upper_diagonal (p : UpperIndex O) (K : SSet.{u}) (x : O) :
    ((upperPlacement O p).obj K).Hom x x =
      (⊥_ (DaggerFreeBC2.BC2 ⥤ SSet.{u})).obj DaggerFreeBC2.point := by
  simp [upper_reconstruction, inverseObj, inverseHom, upperActionParameters,
    Action.functorCategoryEquivalence, Action.FunctorCategoryEquivalence.inverse]

theorem upper_dagger_active (p : UpperIndex O) (K : SSet.{u}) :
    ((upperPlacement O p).obj K).dagger p.val.1 p.val.2 ≍ 𝟙 K := by
  rcases p with ⟨⟨a, b⟩, hab⟩
  simp [upper_reconstruction, inverseObj, inverseDagger, upperActionParameters,
    singleObj, hab]
  exact congr_arg_heq (fun A : SSet.{u} ↦ 𝟙 A) (by simp)

theorem upper_dagger_reverse_active (p : UpperIndex O) (K : SSet.{u}) :
    ((upperPlacement O p).obj K).dagger p.val.2 p.val.1 ≍ 𝟙 K := by
  rcases p with ⟨⟨a, b⟩, hab⟩
  simp [upper_reconstruction, inverseObj, inverseDagger, upperActionParameters,
    singleObj, hab, not_lt_of_gt hab]
  exact congr_arg_heq (fun A : SSet.{u} ↦ 𝟙 A) (by simp)

theorem upper_map_active (p : UpperIndex O) {K L : SSet.{u}} (f : K ⟶ L) :
    ((upperPlacement O p).map f).map p.val.1 p.val.2 ≍ f := by
  rcases p with ⟨⟨a, b⟩, hab⟩
  change inverseMapComponent
    (upperActionMap ⟨(a,b),hab⟩ f) a b ≍ f
  simp [inverseMapComponent, upperActionMap, singleMap, singleObj, hab]

theorem upper_map_reverse_active (p : UpperIndex O) {K L : SSet.{u}} (f : K ⟶ L) :
    ((upperPlacement O p).map f).map p.val.2 p.val.1 ≍ f := by
  rcases p with ⟨⟨a, b⟩, hab⟩
  change inverseMapComponent
    (upperActionMap ⟨(a,b),hab⟩ f) b a ≍ f
  simp [inverseMapComponent, upperActionMap, singleMap, singleObj, hab, not_lt_of_gt hab]

theorem diagonal_active (x : O) (K : SSet.{u}) :
    ((diagonalPlacement O x).obj K).Hom x x =
      ∐ (fun _ : C2 ↦ K) := by
  simp [diagonal_reconstruction, inverseObj, inverseHom, diagonalActionParameters,
    singleObj, Action.functorCategoryEquivalence, Action.FunctorCategoryEquivalence.inverse,
    DaggerFreeBC2.free, evaluationLeftAdjoint]
  rfl

theorem diagonal_inactive (x y : O) (h : y ≠ x) (K : SSet.{u}) :
    ((diagonalPlacement O x).obj K).Hom y y =
      (⊥_ (DaggerFreeBC2.BC2 ⥤ SSet.{u})).obj DaggerFreeBC2.point := by
  simp [diagonal_reconstruction, inverseObj, inverseHom, diagonalActionParameters,
    singleObj, h, Action.functorCategoryEquivalence, Action.FunctorCategoryEquivalence.inverse]

theorem diagonal_upper (x : O) (p : UpperIndex O) (K : SSet.{u}) :
    ((diagonalPlacement O x).obj K).Hom p.val.1 p.val.2 = ⊥_ SSet.{u} := by
  simp [diagonal_reconstruction, inverseObj, inverseHom, diagonalActionParameters,
    emptyUpper, p.property]

theorem diagonal_lower (x : O) (p : UpperIndex O) (K : SSet.{u}) :
    ((diagonalPlacement O x).obj K).Hom p.val.2 p.val.1 = ⊥_ SSet.{u} := by
  simp [diagonal_reconstruction, inverseObj, inverseHom, diagonalActionParameters,
    emptyUpper, p.property, not_lt_of_gt p.property]

theorem diagonal_dagger (x : O) (K : SSet.{u}) :
    ((diagonalPlacement O x).obj K).dagger x x ≍
      (DaggerFreeBC2.free.obj K).map (X := DaggerFreeBC2.point) (Y := DaggerFreeBC2.point)
        DaggerFixedGraph.flip := by
  simp [diagonal_reconstruction, inverseObj, inverseDagger, diagonalActionParameters,
    singleObj, Action.functorCategoryEquivalence, Action.FunctorCategoryEquivalence.inverse]

  exact congr_arg_heq (fun F : DaggerFreeBC2.BC2 ⥤ SSet.{u} ↦
    F.map (X := DaggerFreeBC2.point) (Y := DaggerFreeBC2.point) DaggerFixedGraph.flip)
    (by simp)

theorem diagonal_map (x : O) {K L : SSet.{u}} (f : K ⟶ L) :
    ((diagonalPlacement O x).map f).map x x ≍
      Limits.Sigma.map (fun _ : C2 ↦ f) := by
  change inverseMapComponent
    (diagonalActionMap x f) x x ≍ _
  simp [inverseMapComponent, diagonalActionMap, singleMap, singleObj,
    Action.functorCategoryEquivalence,
    Action.FunctorCategoryEquivalence.inverse, DaggerFreeBC2.free_map_app]

end

end DaggerFixedGraphPlacementData
