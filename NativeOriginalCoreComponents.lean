import NativeOriginalCoreWalkingInverse
import OriginalOrdinaryCoreHomotopyInclusion

/-! Exact original core components detect isomorphisms in the original native homotopy category.
The forward path argument reuses the saved original core-component recognition proof. -/
set_option autoImplicit false
open CategoryTheory Opposite Simplicial MonoidalCategory HomotopicalAlgebra
open DaggerOriginalOrdinaryKanCoreSubcomplex DaggerOriginalOrdinaryCoreHomotopyInclusion
open DaggerOriginalOrdinaryCorePathGroupoid DaggerNativeHoIsoTriangles
open DaggerNativeIhomHoObjects DaggerNativeIhomQuasicategories
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerNativeOriginalCoreComponents
noncomputable section

def vertex (X : SSet.{u}) (x : X _⦋0⦌) : (ordinaryCoreCandidate X : SSet.{u}) _⦋0⦌ :=
  ⟨x, vertex_mem_ordinaryCoreCandidate X x⟩

theorem iso_of_component_eq (X : SSet.{u}) [X.Quasicategory]
    {x y : (ordinaryCoreCandidate X : SSet.{u}) _⦋0⦌}
    (h : SSet.π₀.mk x = SSet.π₀.mk y) :
    Nonempty (SSet.Truncated.HomotopyCategory.mk
      (V := (SSet.truncation 2).obj X) x.val ≅
      SSet.Truncated.HomotopyCategory.mk (V := (SSet.truncation 2).obj X) y.val) := by
  have he := (SSet.π₀.mk_eq_mk_iff x y).1 h
  clear h
  induction he with
  | rel a b hab =>
      obtain ⟨s, rfl, rfl⟩ := hab
      let e := SSet.Edge.mk s rfl rfl
      have : IsIso (SSet.Truncated.HomotopyCategory.homMk e) :=
        core_homMk_isIso X (native_inner_fillers X) e
      exact ⟨(coreHomotopyInclusion X).mapIso
        (asIso (SSet.Truncated.HomotopyCategory.homMk e))⟩
  | refl a => exact ⟨Iso.refl _⟩
  | symm a b hab ih => exact ⟨ih.some.symm⟩
  | trans a b c hab hbc ihab ihbc => exact ⟨ihab.some ≪≫ ihbc.some⟩

theorem component_eq_of_iso (X : SSet.{u}) [X.Quasicategory]
    {x y : (ordinaryCoreCandidate X : SSet.{u}) _⦋0⦌}
    (e : SSet.Truncated.HomotopyCategory.mk
      (V := (SSet.truncation 2).obj X) x.val ≅
      SSet.Truncated.HomotopyCategory.mk (V := (SSet.truncation 2).obj X) y.val) :
    SSet.π₀.mk x = SSet.π₀.mk y := by
  obtain ⟨k, _⟩ := core_edge_preimage_of_isIso X (native_inner_fillers X) e.hom
  exact SSet.π₀.sound k.edge k.src_eq k.tgt_eq

def mapVertexEquiv (A Z : SSet.{u}) :
    (A ⟶ Z) ≃ (ordinaryCoreCandidate ((ihom A).obj Z) : SSet.{u}) _⦋0⦌ where
  toFun f := vertex _ (SSet.hoFunctor.obj.equiv _ (homObject f))
  invFun x := (homObjectEquiv A Z).symm ((SSet.hoFunctor.obj.equiv _).symm x.val)
  left_inv f := by simp [vertex, homObject]
  right_inv x := by
    apply Subtype.ext
    simp [vertex, homObject]

def component {A Z : SSet.{u}} (f : A ⟶ Z) :
    (ordinaryCoreCandidate ((ihom A).obj Z) : SSet.{u}).π₀ :=
  SSet.π₀.mk (mapVertexEquiv A Z f)

theorem component_surjective (A Z : SSet.{u}) :
    Function.Surjective (component (A := A) (Z := Z)) := by
  intro c
  obtain ⟨x, rfl⟩ := SSet.π₀.mk_surjective c
  exact ⟨(mapVertexEquiv A Z).symm x,
    congrArg SSet.π₀.mk ((mapVertexEquiv A Z).apply_symm_apply x)⟩

theorem component_eq_iff {A Z : SSet.{u}} [Z.Quasicategory] (f g : A ⟶ Z) :
    component f = component g ↔ Nonempty (homObject f ≅ homObject g) := by
  have : ((ihom A).obj Z).Quasicategory := ihom_quasicategory A Z
  exact ⟨fun h ↦ iso_of_component_eq _ h, fun ⟨e⟩ ↦ component_eq_of_iso _ e⟩

theorem pre_component {A B Z : SSet.{u}} (f : A ⟶ B) (g : B ⟶ Z) :
    SSet.mapπ₀ (ordinaryCoreCandidateMap ((MonoidalClosed.pre f).app Z)) (component g) =
      component (f ≫ g) := by
  rw [component, SSet.mapπ₀_mk]
  congr 1

theorem weak_core_bijective_components {X Y : SSet.{u}} [X.Quasicategory] [Y.Quasicategory]
    (f : X ⟶ Y) (hf : WeakEquivalence (ordinaryCoreCandidateMap f)) :
    Function.Bijective (SSet.mapπ₀ (ordinaryCoreCandidateMap f)) := by
  have : (ordinaryCoreCandidate X : SSet.{u}).KanComplex :=
    DaggerNativeKanSourceOriginalCoreFactor.native_quasi_core_kan X
  have : (ordinaryCoreCandidate Y : SSet.{u}).KanComplex :=
    DaggerNativeKanSourceOriginalCoreFactor.native_quasi_core_kan Y
  exact ((SSet.weakEquivalence_iff_kanComplexW _).mp hf).bijective_mapπ₀

end
end DaggerNativeOriginalCoreComponents
