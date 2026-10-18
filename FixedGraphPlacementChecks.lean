import FixedGraphPlacementData
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal

/-! Scope and full category-data checks for arbitrary original O and common universe u. -/

open CategoryTheory Limits DaggerModels DaggerFixedGraph DaggerPlacementStructure
open DaggerFixedGraphPlacements DaggerFixedGraphPlacementData
open FixedDaggerSimplicialGraph

universe u

namespace DaggerFixedGraphPlacementChecks

noncomputable section

variable {O : Type u}
local instance : LinearOrder O := chosenLinearOrder O

/-- Initial BC₂ diagrams have initial underlying simplicial sets,
by actual evaluation preservation. -/
def emptyDiagonalUnderlyingIsInitial :
    IsInitial ((⊥_ (DaggerFreeBC2.BC2 ⥤ SSet.{u})).obj DaggerFreeBC2.point) := by
  letI : PreservesColimits DaggerFreeBC2.ev.{u} := by
    dsimp [DaggerFreeBC2.ev]
    infer_instance
  exact initialIsInitial.isInitialObj DaggerFreeBC2.ev.{u} _

def upperInactiveDiagonalIsInitial (p : UpperIndex O) (K : SSet.{u}) (x : O) :
    IsInitial (((upperPlacement O p).obj K).Hom x x) := by
  rw [upper_diagonal]
  exact emptyDiagonalUnderlyingIsInitial

def diagonalInactiveIsInitial (x y : O) (h : y ≠ x) (K : SSet.{u}) :
    IsInitial (((diagonalPlacement O x).obj K).Hom y y) := by
  rw [diagonal_inactive x y h]
  exact emptyDiagonalUnderlyingIsInitial

theorem upper_map_reconstruction (p : UpperIndex O) {K L : SSet.{u}} (f : K ⟶ L) :
    (upperPlacement O p).map f = inverseMap (upperActionMap p f) := rfl

theorem diagonal_map_reconstruction (x : O) {K L : SSet.{u}} (f : K ⟶ L) :
    (diagonalPlacement O x).map f = inverseMap (diagonalActionMap x f) := rfl

theorem upper_inactive_map (p q : UpperIndex O) (h : q ≠ p) {K L : SSet.{u}} (f : K ⟶ L) :
    ((upperPlacement O p).map f).map q.val.1 q.val.2 ≍ 𝟙 (⊥_ SSet.{u}) := by
  rw [upper_map_reconstruction]
  simp [inverseMap, inverseMapComponent, upperActionMap, singleMap, singleObj, q.property, h ]

  exact (eqToHom_heq_id_cod _ _ _).trans
    (congr_arg_heq (fun A : SSet.{u} ↦ 𝟙 A) (by simp [h]))

theorem upper_inactive_reverse_map (p q : UpperIndex O) (h : q ≠ p)
    {K L : SSet.{u}} (f : K ⟶ L) :
    ((upperPlacement O p).map f).map q.val.2 q.val.1 ≍ 𝟙 (⊥_ SSet.{u}) := by
  rw [upper_map_reconstruction]
  simp [inverseMap, inverseMapComponent, upperActionMap, singleMap, singleObj, q.property, h,
    not_lt_of_gt q.property ]

  exact (eqToHom_heq_id_cod _ _ _).trans
    (congr_arg_heq (fun A : SSet.{u} ↦ 𝟙 A) (by simp [h]))

theorem upper_diagonal_map (p : UpperIndex O) {K L : SSet.{u}} (f : K ⟶ L) (x : O) :
    ((upperPlacement O p).map f).map x x ≍
      𝟙 ((⊥_ (DaggerFreeBC2.BC2 ⥤ SSet.{u})).obj DaggerFreeBC2.point) := by
  rw [upper_map_reconstruction]
  simp [inverseMap, inverseMapComponent, upperActionMap, upperActionParameters,
    Action.functorCategoryEquivalence, Action.FunctorCategoryEquivalence.inverse]

theorem diagonal_inactive_map (x y : O) (h : y ≠ x) {K L : SSet.{u}} (f : K ⟶ L) :
    ((diagonalPlacement O x).map f).map y y ≍
      𝟙 ((⊥_ (DaggerFreeBC2.BC2 ⥤ SSet.{u})).obj DaggerFreeBC2.point) := by
  rw [diagonal_map_reconstruction]
  simp [inverseMap, inverseMapComponent, diagonalActionMap, singleMap, singleObj, h,
    Action.functorCategoryEquivalence, Action.FunctorCategoryEquivalence.inverse ]

  exact (eqToHom_heq_id_cod _ _ _).trans
    (congr_arg_heq (fun A : SSet.{u} ↦ 𝟙 A) (by simp [h]))

theorem diagonal_offdiagonal_map (x : O) (p : UpperIndex O) {K L : SSet.{u}} (f : K ⟶ L) :
    ((diagonalPlacement O x).map f).map p.val.1 p.val.2 ≍ 𝟙 (⊥_ SSet.{u}) := by
  rw [diagonal_map_reconstruction]
  simp [inverseMap, inverseMapComponent, diagonalActionMap, diagonalActionParameters,
    emptyUpper, p.property]

theorem diagonal_reverse_map (x : O) (p : UpperIndex O) {K L : SSet.{u}} (f : K ⟶ L) :
    ((diagonalPlacement O x).map f).map p.val.2 p.val.1 ≍ 𝟙 (⊥_ SSet.{u}) := by
  rw [diagonal_map_reconstruction]
  simp [inverseMap, inverseMapComponent, diagonalActionMap, diagonalActionParameters,
    emptyUpper, p.property,
    not_lt_of_gt p.property]

def diagonalFiberIso (x : O) (K : SSet.{u}) :
    ((diagonalPlacement O x).obj K).Hom x x ≅ ∐ (fun _ : C2 ↦ K) :=
  eqToIso (diagonal_active x K)

theorem diagonal_dagger_full (x : O) (K : SSet.{u}) :
    (diagonalFiberIso x K).inv ≫ ((diagonalPlacement O x).obj K).dagger x x ≫
      (diagonalFiberIso x K).hom =
        (DaggerFreeBC2.free.obj K).map (X := DaggerFreeBC2.point) (Y := DaggerFreeBC2.point)
          DaggerFixedGraph.flip := by
  apply eq_of_heq
  have hi : (diagonalFiberIso x K).inv ≍ 𝟙 (∐ fun _ : C2 ↦ K) := by
    simp [diagonalFiberIso, eqToHom_heq_id_dom]
  have hh : (diagonalFiberIso x K).hom ≍ 𝟙 (∐ fun _ : C2 ↦ K) := by
    simp [diagonalFiberIso, eqToHom_heq_id_cod]
  exact (heq_comp rfl (diagonal_active x K) rfl
    (heq_comp rfl (diagonal_active x K) (diagonal_active x K)
      hi (diagonal_dagger x K)) hh).trans (heq_of_eq (by simp))

theorem diagonal_swap_one (x : O) (K : SSet.{u}) :
    Sigma.ι (fun _ : C2 ↦ K) 1 ≫ (diagonalFiberIso x K).inv ≫
      ((diagonalPlacement O x).obj K).dagger x x ≫ (diagonalFiberIso x K).hom =
        Sigma.ι (fun _ : C2 ↦ K) DaggerFixedGraph.flip := by
  rw [diagonal_dagger_full]
  exact DaggerFreeBC2.free_flip_one K

theorem diagonal_swap_flip (x : O) (K : SSet.{u}) :
    Sigma.ι (fun _ : C2 ↦ K) DaggerFixedGraph.flip ≫ (diagonalFiberIso x K).inv ≫
      ((diagonalPlacement O x).obj K).dagger x x ≫ (diagonalFiberIso x K).hom =
        Sigma.ι (fun _ : C2 ↦ K) 1 := by
  rw [diagonal_dagger_full]
  exact DaggerFreeBC2.free_flip_flip K

theorem diagonal_map_full (x : O) {K L : SSet.{u}} (f : K ⟶ L) :
    (diagonalFiberIso x K).inv ≫ ((diagonalPlacement O x).map f).map x x ≫
      (diagonalFiberIso x L).hom = Limits.Sigma.map (fun _ : C2 ↦ f) := by
  apply eq_of_heq
  have hi : (diagonalFiberIso x K).inv ≍ 𝟙 (∐ fun _ : C2 ↦ K) := by
    simp [diagonalFiberIso, eqToHom_heq_id_dom]
  have hh : (diagonalFiberIso x L).hom ≍ 𝟙 (∐ fun _ : C2 ↦ L) := by
    simp [diagonalFiberIso, eqToHom_heq_id_cod]
  exact (heq_comp rfl (diagonal_active x L) rfl
    (heq_comp rfl (diagonal_active x K) (diagonal_active x L)
      hi (diagonal_map x f)) hh).trans (heq_of_eq (by simp))

theorem diagonal_map_copy (x : O) {K L : SSet.{u}} (f : K ⟶ L) (g : C2) :
    Sigma.ι (fun _ : C2 ↦ K) g ≫ (diagonalFiberIso x K).inv ≫
      ((diagonalPlacement O x).map f).map x x ≫ (diagonalFiberIso x L).hom =
        f ≫ Sigma.ι (fun _ : C2 ↦ L) g := by
  rw [diagonal_map_full]
  simp

theorem upper_original_object (p : UpperIndex O) (K : SSet.{u}) :
    ((upperPlacement O p).obj K).toGraph.Obj = O := rfl

theorem diagonal_original_object (x : O) (K : SSet.{u}) :
    ((diagonalPlacement O x).obj K).toGraph.Obj = O := rfl

theorem upper_identity_object_map (p : UpperIndex O) {K L : SSet.{u}} (f : K ⟶ L) :
    (toGraphMap ((upperPlacement O p).map f)).obj = id := rfl

theorem diagonal_identity_object_map (x : O) {K L : SSet.{u}} (f : K ⟶ L) :
    (toGraphMap ((diagonalPlacement O x).map f)).obj = id := rfl

theorem upper_left_triangle (p : UpperIndex O) (K : SSet.{u}) :
    (upperPlacement O p).map ((upperAdjunction O p).unit.app K) ≫
      (upperAdjunction O p).counit.app ((upperPlacement O p).obj K) =
        𝟙 ((upperPlacement O p).obj K) := (upperAdjunction O p).left_triangle_components K

theorem upper_right_triangle (p : UpperIndex O) (G : FixedDaggerSimplicialGraph O) :
    (upperAdjunction O p).unit.app ((homEval O p.val.1 p.val.2).obj G) ≫
      (homEval O p.val.1 p.val.2).map ((upperAdjunction O p).counit.app G) =
        𝟙 ((homEval O p.val.1 p.val.2).obj G) := (upperAdjunction O p).right_triangle_components G

theorem diagonal_left_triangle (x : O) (K : SSet.{u}) :
    (diagonalPlacement O x).map ((diagonalAdjunction O x).unit.app K) ≫
      (diagonalAdjunction O x).counit.app ((diagonalPlacement O x).obj K) =
        𝟙 ((diagonalPlacement O x).obj K) := (diagonalAdjunction O x).left_triangle_components K

theorem diagonal_right_triangle (x : O) (G : FixedDaggerSimplicialGraph O) :
    (diagonalAdjunction O x).unit.app ((homEval O x x).obj G) ≫
      (homEval O x x).map ((diagonalAdjunction O x).counit.app G) =
        𝟙 ((homEval O x x).obj G) := (diagonalAdjunction O x).right_triangle_components G

theorem upper_unit_naturality (p : UpperIndex O) {K L : SSet.{u}} (f : K ⟶ L) :
    f ≫ (upperAdjunction O p).unit.app L = (upperAdjunction O p).unit.app K ≫
      (homEval O p.val.1 p.val.2).map ((upperPlacement O p).map f) :=
  ((upperAdjunction O p).unit.naturality f)

theorem upper_counit_naturality (p : UpperIndex O)
    {G H : FixedDaggerSimplicialGraph O} (f : G ⟶ H) :
    (upperPlacement O p).map ((homEval O p.val.1 p.val.2).map f) ≫
      (upperAdjunction O p).counit.app H = (upperAdjunction O p).counit.app G ≫ f :=
  (upperAdjunction O p).counit.naturality f

theorem diagonal_unit_naturality (x : O) {K L : SSet.{u}} (f : K ⟶ L) :
    f ≫ (diagonalAdjunction O x).unit.app L = (diagonalAdjunction O x).unit.app K ≫
      (homEval O x x).map ((diagonalPlacement O x).map f) :=
  ((diagonalAdjunction O x).unit.naturality f)

theorem diagonal_counit_naturality (x : O)
    {G H : FixedDaggerSimplicialGraph O} (f : G ⟶ H) :
    (diagonalPlacement O x).map ((homEval O x x).map f) ≫
      (diagonalAdjunction O x).counit.app H = (diagonalAdjunction O x).counit.app G ≫ f :=
  (diagonalAdjunction O x).counit.naturality f

end

end DaggerFixedGraphPlacementChecks
