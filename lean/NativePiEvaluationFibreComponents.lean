import NativePiHornBoundaryComponents
import NativeHornPointWeakEquivalences
import NativeAnodyneRelativeMappingRelaxation
import NativePointEvaluationMappingFibreIso

/-! Original native pi_n is the actual component set of boundary-sphere point-evaluation fibres. -/
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory MonoidalClosed Simplicial HomotopicalAlgebra
open CartesianMonoidalCategory
open SSet.KanComplex DaggerNativePiHornBoundaryComponents
open DaggerNativePushoutConstantMappingFibres DaggerNativeHornPointWeakEquivalences
open DaggerNativeAnodyneRelativeMappingRelaxation DaggerNativePointEvaluationMappingFibreIso
open DaggerOriginalFixedObjectCotensorPoints DaggerOriginalSimplicialPiZeroWeakEquivalence
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerNativePiEvaluationFibreComponents
noncomputable section

theorem horn_point_relaxation_weak (n : ℕ) (i : Fin (n + 2))
    (a : 𝟙_ SSet.{u} ⟶ (SSet.horn (n + 1) i : SSet.{u}))
    (X : SSet.{u}) [IsFibrant X] (x : X _⦋0⦌) :
    WeakEquivalence (relaxationMap a
      (SSet.Subcomplex.homOfLE (SSet.horn_le_boundary i)) X x) := by
  have : Mono a := ⟨fun f g _ ↦ isTerminalTensorUnit.hom_ext f g⟩
  have ha : SSet.anodyneExtensions a :=
    (DaggerOrdinaryAnodyneTensor.anodyne_iff_trivialCofibration a).mpr
      (horn_global_point_trivialCofibration n i a)
  exact relaxationMap_weak a _ ha X x

def piToEvaluationComponent (n : ℕ) (i : Fin (n + 2))
    (a : 𝟙_ SSet.{u} ⟶ (SSet.horn (n + 1) i : SSet.{u}))
    (X : SSet.{u}) [IsFibrant X] (x : X _⦋0⦌) :
    π n X x → (SSet.Subcomplex.fiber
      (pointEvaluation (a ≫ SSet.Subcomplex.homOfLE (SSet.horn_le_boundary i)) X) x :
        SSet.{u}).π₀ :=
  fun p ↦ SSet.mapπ₀ (pointFibreIso
    (a ≫ SSet.Subcomplex.homOfLE (SSet.horn_le_boundary i)) X x).hom
    (SSet.mapπ₀ (relaxationMap a
      (SSet.Subcomplex.homOfLE (SSet.horn_le_boundary i)) X x)
      (piHornComponentsEquiv n i X x p))

theorem piToEvaluationComponent_bijective (n : ℕ) (i : Fin (n + 2))
    (a : 𝟙_ SSet.{u} ⟶ (SSet.horn (n + 1) i : SSet.{u}))
    (X : SSet.{u}) [IsFibrant X] (x : X _⦋0⦌) :
    Function.Bijective (piToEvaluationComponent n i a X x) := by
  have := horn_point_relaxation_weak n i a X x
  exact (bijective_mapPiZero (pointFibreIso
    (a ≫ SSet.Subcomplex.homOfLE (SSet.horn_le_boundary i)) X x).hom).comp
      ((bijective_mapPiZero (relaxationMap a
        (SSet.Subcomplex.homOfLE (SSet.horn_le_boundary i)) X x)).comp
          (piHornComponentsEquiv n i X x).bijective)

def piEvaluationFibreEquiv (n : ℕ) (i : Fin (n + 2))
    (a : 𝟙_ SSet.{u} ⟶ (SSet.horn (n + 1) i : SSet.{u}))
    (X : SSet.{u}) [IsFibrant X] (x : X _⦋0⦌) :
    π n X x ≃ (SSet.Subcomplex.fiber
      (pointEvaluation (a ≫ SSet.Subcomplex.homOfLE (SSet.horn_le_boundary i)) X) x :
        SSet.{u}).π₀ :=
  Equiv.ofBijective (piToEvaluationComponent n i a X x)
    (piToEvaluationComponent_bijective n i a X x)

theorem piEvaluationFibreEquiv_inclusion (n : ℕ) (i : Fin (n + 2))
    (a : 𝟙_ SSet.{u} ⟶ (SSet.horn (n + 1) i : SSet.{u}))
    (X : SSet.{u}) [IsFibrant X] (x : X _⦋0⦌) (p : π n X x) :
    SSet.mapπ₀ (SSet.Subcomplex.fiber
      (pointEvaluation (a ≫ SSet.Subcomplex.homOfLE (SSet.horn_le_boundary i)) X) x).ι
        (piEvaluationFibreEquiv n i a X x p) =
      SSet.mapπ₀ (hornMappingSpace n i X x).ι (piHornComponentsEquiv n i X x p) := by
  change SSet.mapπ₀ _ (SSet.mapπ₀ _ (SSet.mapπ₀ _ (piHornComponentsEquiv n i X x p))) = _
  rw [← SSet.mapπ₀_comp_apply, pointFibreIso_hom_ι,
    ← SSet.mapπ₀_comp_apply, relaxationMap_ι]

theorem piEvaluationFibreEquiv_mk_lift (n : ℕ) (i : Fin (n + 2))
    (a : 𝟙_ SSet.{u} ⟶ (SSet.horn (n + 1) i : SSet.{u}))
    (X : SSet.{u}) [IsFibrant X] (x : X _⦋0⦌) (f : X.PtSimplex n x) :
    ∃ v : (SSet.Subcomplex.fiber
      (pointEvaluation (a ≫ SSet.Subcomplex.homOfLE (SSet.horn_le_boundary i)) X) x :
        SSet.{u}) _⦋0⦌,
      ((MonoidalClosed.pre (SSet.Subcomplex.homOfLE (SSet.horn_le_boundary i))).app X).app _
        v.val = SSet.ihom₀Equiv.symm (SSet.const x) ∧
      ((MonoidalClosed.pre (SSet.boundary.ι i)).app X).app _ v.val =
        SSet.ihom₀Equiv.symm f.map ∧
      piEvaluationFibreEquiv n i a X x (π.mk f) = SSet.π₀.mk v := by
  let u := SSet.Subcomplex.RelativeMorphism.equiv f
  let w := (sphereHornMappingIso n i X x).inv.app _ u
  let v := (pointFibreIso
    (a ≫ SSet.Subcomplex.homOfLE (SSet.horn_le_boundary i)) X x).hom.app _
    ((relaxationMap a (SSet.Subcomplex.homOfLE (SSet.horn_le_boundary i)) X x).app _ w)
  refine ⟨v, ?_, ?_, ?_⟩
  · change ((MonoidalClosed.pre
      (SSet.Subcomplex.homOfLE (SSet.horn_le_boundary i))).app X).app _ w.val = _
    exact (SSet.Subcomplex.mem_fiber_obj_zero_iff _ _ _).mp w.property
  · have ht := congrFun (NatTrans.congr_app
      (restrictionFibreIso_hom_ι
        (DaggerNativeHornBoundaryAttachment.boundary_horn_missing_face_isPushout n i).flip X x)
      (Opposite.op ⦋0⦌)) w
    change ((sphereHornMappingIso n i X x).hom.app _ w).val =
      ((MonoidalClosed.pre (SSet.boundary.ι i)).app X).app _ w.val at ht
    have hw : (sphereHornMappingIso n i X x).hom.app _ w = u :=
      congrFun (NatTrans.congr_app (Iso.inv_hom_id (sphereHornMappingIso n i X x)) _) u
    rw [hw] at ht
    exact ht.symm
  · rfl

end
end DaggerNativePiEvaluationFibreComponents
