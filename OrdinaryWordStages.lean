import OrdinaryWordLength
import Mathlib.CategoryTheory.Limits.Types.Pushouts
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks

/-! Successor pushouts for the actual length stages in the original quotient Hom.
The attaching map is the original word evaluation restricted to its full boundary. -/

open CategoryTheory Limits HomotopicalAlgebra DaggerModels
open scoped SSet.modelCategoryQuillen
open DaggerRelativeOneCellPresentation DaggerOrdinaryReducedWords DaggerOrdinaryWordBoundary
open DaggerOrdinaryCellNormalizer DaggerOrdinaryWordLength

universe u

namespace DaggerOrdinaryWordStages

noncomputable section

variable (C : SimplicialCat.{u, u}) (x y : C.Obj) {L : SSet.{u}}
variable (A : L.Subcomplex) (uA : (A : SSet.{u}) ⟶ (x ⟶[SSet] y))

/-- The original inclusions of consecutive length-bounded subcomplexes. -/
def step (n : ℕ) (a b : C.Obj) :
    (stage C x y A uA n a b : SSet.{u}) ⟶ (stage C x y A uA (n + 1) a b : SSet.{u}) :=
  SSet.Subcomplex.homOfLE (stage_monotone C x y A uA a b (Nat.le_succ n))

@[reassoc] theorem step_ι (n : ℕ) (a b : C.Obj) :
    step C x y A uA n a b ≫ (stage C x y A uA (n + 1) a b).ι =
      (stage C x y A uA n a b).ι := rfl

instance step_mono (n : ℕ) (a b : C.Obj) : Mono (step C x y A uA n a b) :=
  inferInstanceAs (Mono (SSet.Subcomplex.homOfLE
    (stage_monotone C x y A uA a b (Nat.le_succ n))))

theorem boundaryEvaluation_range_le (n : ℕ) (a b : C.Obj) :
    SSet.Subcomplex.range
      ((Boundary C x y A (n + 1) a b).ι ≫ wordEvaluation C x y A uA (n + 1) a b) ≤
        stage C x y A uA n a b := by
  intro q z hz
  rcases hz with ⟨w, rfl⟩
  exact (wordEvaluation_mem_previous_stage_iff_boundary C x y A uA q n a b w.val).2
    w.property

/-- Replace all attaching letters using the same original quotient relations. -/
def boundaryToStage (n : ℕ) (a b : C.Obj) :
    (Boundary C x y A (n + 1) a b : SSet.{u}) ⟶ (stage C x y A uA n a b : SSet.{u}) :=
  SSet.Subcomplex.lift
    ((Boundary C x y A (n + 1) a b).ι ≫ wordEvaluation C x y A uA (n + 1) a b)
    (boundaryEvaluation_range_le C x y A uA n a b)

@[reassoc] theorem boundaryToStage_ι (n : ℕ) (a b : C.Obj) :
    boundaryToStage C x y A uA n a b ≫ (stage C x y A uA n a b).ι =
      (Boundary C x y A (n + 1) a b).ι ≫ wordEvaluation C x y A uA (n + 1) a b := rfl

theorem attachment_commutes (n : ℕ) (a b : C.Obj) :
    boundaryToStage C x y A uA n a b ≫ step C x y A uA n a b =
      (Boundary C x y A (n + 1) a b).ι ≫ wordToStage C x y A uA (n + 1) a b := by
  ext q w
  rfl

/-- The intersection with the preceding stage is precisely the entire word boundary. -/
theorem attachment_app_isPullback (n : ℕ) (a b : C.Obj) (q : SimplexCategoryᵒᵖ) :
    IsPullback ((boundaryToStage C x y A uA n a b).app q)
      ((Boundary C x y A (n + 1) a b).ι.app q) ((step C x y A uA n a b).app q)
      ((wordToStage C x y A uA (n + 1) a b).app q) := by
  rw [Types.isPullback_iff]
  refine ⟨NatTrans.congr_app (attachment_commutes C x y A uA n a b) q, ?_, ?_⟩
  · intro v w h
    exact Subtype.ext h.2
  · intro z w he
    have hv := congrArg Subtype.val he
    change z.val = (wordEvaluation C x y A uA (n + 1) a b).app q w at hv
    have hw : w ∈ (Boundary C x y A (n + 1) a b).obj q := by
      apply (wordEvaluation_mem_previous_stage_iff_boundary C x y A uA q n a b w).1
      rw [← hv]
      exact z.property
    exact ⟨⟨w, hw⟩, Subtype.ext hv.symm, rfl⟩

theorem stage_coverage (n : ℕ) (a b : C.Obj) (q : SimplexCategoryᵒᵖ)
    (z : (stage C x y A uA (n + 1) a b : SSet.{u}).obj q) :
    z ∈ Set.range ((step C x y A uA n a b).app q) ∨
      z ∈ Set.range ((wordToStage C x y A uA (n + 1) a b).app q) := by
  have hz := z.property
  change (normalize C x y A uA q a b z.val).1 ≤ n + 1 at hz
  generalize hred : normalize C x y A uA q a b z.val = red at hz
  rcases red with ⟨k, w⟩
  change k ≤ n + 1 at hz
  by_cases hk : k ≤ n
  · apply Or.inl
    refine ⟨⟨z.val, ?_⟩, rfl⟩
    change (normalize C x y A uA q a b z.val).1 ≤ n
    rwa [hred]
  · have hk' : k = n + 1 := by omega
    subst k
    apply Or.inr
    have hd := decodeClass_normalize C x y A uA q a b z.val
    rw [hred] at hd
    exact ⟨w.val, Subtype.ext hd⟩

theorem wordToStage_injective_outside_boundary (n : ℕ) (a b : C.Obj)
    (q : SimplexCategoryᵒᵖ) (v w : (Word C x y L (n + 1) a b).obj q)
    (hv : v ∉ (Boundary C x y A (n + 1) a b).obj q)
    (hw : w ∉ (Boundary C x y A (n + 1) a b).obj q)
    (he : (wordToStage C x y A uA (n + 1) a b).app q v =
      (wordToStage C x y A uA (n + 1) a b).app q w) : v = w := by
  have h := congrArg (normalize C x y A uA q a b) (congrArg Subtype.val he)
  change normalize C x y A uA q a b ((wordEvaluation C x y A uA (n + 1) a b).app q v) =
    normalize C x y A uA q a b ((wordEvaluation C x y A uA (n + 1) a b).app q w) at h
  rw [normalize_word_outside_boundary C x y A uA q (n + 1) a b v hv,
    normalize_word_outside_boundary C x y A uA q (n + 1) a b w hw] at h
  exact congrArg Subtype.val (eq_of_heq (Sigma.mk.inj_iff.mp h).2)

/-- Reuse the Types criterion: exact intersection, joint coverage and unique interiors. -/
theorem attachment_app_isPushout (n : ℕ) (a b : C.Obj) (q : SimplexCategoryᵒᵖ) :
    IsPushout ((boundaryToStage C x y A uA n a b).app q)
      ((Boundary C x y A (n + 1) a b).ι.app q) ((step C x y A uA n a b).app q)
      ((wordToStage C x y A uA (n + 1) a b).app q) := by
  apply Types.isPushout_of_isPullback_of_mono'
    (attachment_app_isPullback C x y A uA n a b q)
  · exact Set.eq_univ_of_forall (stage_coverage C x y A uA n a b q)
  · intro v w hv hw he
    apply wordToStage_injective_outside_boundary C x y A uA n a b q v w _ _ he
    · exact fun h ↦ hv ⟨⟨v, h⟩, rfl⟩
    · exact fun h ↦ hw ⟨⟨w, h⟩, rfl⟩

/-- This is the actual simplicial pushout on the same original quotient Hom. -/
theorem attachment_isPushout (n : ℕ) (a b : C.Obj) :
    IsPushout (boundaryToStage C x y A uA n a b) (Boundary C x y A (n + 1) a b).ι
      (step C x y A uA n a b) (wordToStage C x y A uA (n + 1) a b) := by
  apply IsPushout.of_isColimit
    (c := PushoutCocone.mk (step C x y A uA n a b) (wordToStage C x y A uA (n + 1) a b)
      (attachment_commutes C x y A uA n a b))
  apply evaluationJointlyReflectsColimits
  intro q
  exact (isColimitMapCoconePushoutCoconeEquiv ((evaluation _ (Type u)).obj q)
    (attachment_commutes C x y A uA n a b)).symm
      (attachment_app_isPushout C x y A uA n a b q).isColimit

theorem step_anodyne (hA : SSet.anodyneExtensions A.ι) (n : ℕ) (a b : C.Obj) :
    SSet.anodyneExtensions (step C x y A uA n a b) :=
  MorphismProperty.of_isPushout (attachment_isPushout C x y A uA n a b)
    (boundary_anodyne C x y A hA n a b)

theorem step_trivialCofibration (hA : SSet.anodyneExtensions A.ι) (n : ℕ) (a b : C.Obj) :
    trivialCofibrations SSet.{u} (step C x y A uA n a b) :=
  (DaggerOrdinaryAnodyneTensor.anodyne_iff_trivialCofibration _).1
    (step_anodyne C x y A uA hA n a b)

end

end DaggerOrdinaryWordStages
