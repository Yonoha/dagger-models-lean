import NativeAmbientDaggerHomEvaluation
import NativeRelativeIhomTrivialFibration
import NativeAmbientDaggerCotensorFibrations

/-! The ORIGINAL relative ambient dagger cotensor is a genuine pullback.
Its EVERY original Hom map is the SAME native SSet relative internal-Hom map.
-/
set_option autoImplicit false
open CategoryTheory Limits HomotopicalAlgebra DaggerModels MonoidalClosed
open DaggerOriginalFixedObjectDaggerCategories DaggerOriginalFixedObjectCotensors
open DaggerNativeAmbientDaggerHomEvaluation
open scoped SSet.modelCategoryQuillen DaggerOriginalFixedObjectAmbientDaggerModel
universe u
namespace DaggerNativeAmbientDaggerRelativeCotensor
noncomputable section

variable {O : Type u} {K L : SSet.{u}} (j : K ⟶ L)
variable {C D : FixedDaggerCategory O} (p : C ⟶ D)

def target : FixedDaggerCategory O :=
  pullback (daggerCotensorMap K p) (daggerCotensorPre j D)

def relativeMap : daggerCotensor L C ⟶ target j p :=
  pullback.lift (daggerCotensorPre j C) (daggerCotensorMap L p)
    (daggerCotensorPre_map j p).symm

theorem relativeMap_fst : relativeMap j p ≫
    pullback.fst (daggerCotensorMap K p) (daggerCotensorPre j D) = daggerCotensorPre j C := by
  simp only [relativeMap, pullback.lift_fst]

theorem relativeMap_snd : relativeMap j p ≫
    pullback.snd (daggerCotensorMap K p) (daggerCotensorPre j D) = daggerCotensorMap L p := by
  simp only [relativeMap, pullback.lift_snd]

def homPullback (x y : O) : SSet.PullbackIhom j (p.underlying.map x y) where
  pt := (target j p).underlying.enriched.Hom x y
  fst := (pullback.fst (daggerCotensorMap K p) (daggerCotensorPre j D)).underlying.map x y
  snd := (pullback.snd (daggerCotensorMap K p) (daggerCotensorPre j D)).underlying.map x y
  isPullback := map_isPullback x y (IsPullback.of_hasPullback
    (daggerCotensorMap K p) (daggerCotensorPre j D))

theorem relativeMap_hom (x y : O) :
    (relativeMap j p).underlying.map x y = (homPullback j p x y).π := by
  apply (homPullback j p x y).isPullback.hom_ext
  · rw [(homPullback j p x y).π_fst]
    change (homEval O x y).map (relativeMap j p) ≫
      (homEval O x y).map (pullback.fst _ _) = _
    rw [← Functor.map_comp, relativeMap_fst]
    rfl
  · rw [(homPullback j p x y).π_snd]
    change (homEval O x y).map (relativeMap j p) ≫
      (homEval O x y).map (pullback.snd _ _) = _
    rw [← Functor.map_comp, relativeMap_snd]
    rfl

theorem relativeMap_fibration [Mono j] [Fibration p] : Fibration (relativeMap j p) := by
  rw [DaggerOriginalFixedObjectAmbientDaggerModel.fibration_iff_original]
  intro x y
  have : Fibration (p.underlying.map x y) :=
    (DaggerOriginalFixedObjectAmbientDaggerModel.fibration_iff_original p).mp inferInstance x y
  rw [relativeMap_hom]
  infer_instance

theorem relativeMap_trivialFibration [Mono j] [Fibration p] [WeakEquivalence p] :
    trivialFibrations (FixedDaggerCategory O) (relativeMap j p) := by
  rw [mem_trivialFibrations_iff]
  refine ⟨relativeMap_fibration j p, ?_⟩
  rw [DaggerOriginalFixedObjectAmbientDaggerModel.weakEquivalence_iff_original]
  intro x y
  have : Fibration (p.underlying.map x y) :=
    (DaggerOriginalFixedObjectAmbientDaggerModel.fibration_iff_original p).mp inferInstance x y
  have : WeakEquivalence (p.underlying.map x y) :=
    (DaggerOriginalFixedObjectAmbientDaggerModel.weakEquivalence_iff_original p).mp
      inferInstance x y
  rw [relativeMap_hom]
  exact ((mem_trivialFibrations_iff _).mp
    (DaggerNativeRelativeIhomTrivialFibration.mono_left_trivial_right j
      (p.underlying.map x y) (homPullback j p x y))).2

theorem relativeMap_anodyne_trivialFibration (hj : SSet.anodyneExtensions j) [Fibration p] :
    trivialFibrations (FixedDaggerCategory O) (relativeMap j p) := by
  rw [mem_trivialFibrations_iff,
    DaggerOriginalFixedObjectAmbientDaggerModel.fibration_iff_original,
    DaggerOriginalFixedObjectAmbientDaggerModel.weakEquivalence_iff_original]
  constructor
  · intro x y
    have : Fibration (p.underlying.map x y) :=
      (DaggerOriginalFixedObjectAmbientDaggerModel.fibration_iff_original p).mp inferInstance x y
    rw [relativeMap_hom]
    exact ((mem_trivialFibrations_iff _).mp
      (DaggerOriginalSimplicialCotensorRestriction.relative_anodyne_trivialFibration j hj
        (p.underlying.map x y) (homPullback j p x y))).1
  · intro x y
    have : Fibration (p.underlying.map x y) :=
      (DaggerOriginalFixedObjectAmbientDaggerModel.fibration_iff_original p).mp inferInstance x y
    rw [relativeMap_hom]
    exact ((mem_trivialFibrations_iff _).mp
      (DaggerOriginalSimplicialCotensorRestriction.relative_anodyne_trivialFibration j hj
        (p.underlying.map x y) (homPullback j p x y))).2

end
end DaggerNativeAmbientDaggerRelativeCotensor
