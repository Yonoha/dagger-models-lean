import NativeKanTrivialCofibrationWalkingRetract
import NativeKanSourceOriginalCoreFactor
import NativeMonoRestrictionRelativeWalkingLifting
import NativeWalkingHomotopySectionCorrection

/-! Whole relative J lifting gives native Kan fibrations on the exact ordinary cores. -/
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory Simplicial HomotopicalAlgebra
open DaggerActualFreeWalkingIsoIntegerObstruction DaggerActualFreeAntiWalkingCategoricalCylinder
open DaggerOriginalOrdinaryKanCoreSubcomplex DaggerNativeKanSourceOriginalCoreFactor
open DaggerNativeKanTrivialCofibrationWalkingRetract DaggerNativeIhomQuasicategories
open DaggerNativeMonoRestrictionRelativeWalkingLifting DaggerNativeWalkingHomotopySectionCorrection
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerNativeRelativeWalkingCoreFibration
noncomputable section

theorem core_lifts_Kan_trivial {E X : SSet.{u}} (p : E ⟶ X)
    (hp : ∀ {K L : SSet.{u}} (j : K ⟶ L) [Mono j]
      (sq : SSet.PushoutTensor j zeroInclusion.{u}), HasLiftingProperty sq.ι p)
    {K L : SSet.{u}} [K.KanComplex] [L.KanComplex] (j : K ⟶ L)
    [Cofibration j] [WeakEquivalence j] : HasLiftingProperty j (ordinaryCoreCandidateMap p) := by
  constructor
  intro a b comm
  obtain ⟨r, H, hjr, h0, h1, hrel⟩ := exists_relative_walking_retract j
  let a' := a ≫ (ordinaryCoreCandidate E).ι
  let b' := b ≫ (ordinaryCoreCandidate X).ι
  have hw : a' ≫ p = j ≫ b' := by
    dsimp [a', b']
    rw [Category.assoc, ← ordinaryCoreCandidateMap_comp_ι, ← Category.assoc,
      comm.w, Category.assoc]
  let sq : SSet.PushoutTensor j zeroInclusion.{u} :=
    Functor.PushoutObjObj.ofHasPushout _ _ _
  let g0 := fst L (Δ[0] : SSet.{u}) ≫ r ≫ a'
  let gK := fst K J.{u} ≫ a'
  have w : (j ▷ (Δ[0] : SSet.{u})) ≫ g0 = (K ◁ zeroInclusion.{u}) ≫ gK := by
    apply NatTrans.ext
    funext q t
    change a'.app q (r.app q (j.app q t.1)) = a'.app q t.1
    exact congrArg (a'.app q) (congrFun (NatTrans.congr_app hjr q) t.1)
  let top := sq.isPushout.desc g0 gK w
  let bottom := H ≫ b'
  have h0b : intervalEndpoint L false ≫ (H ≫ b') = (r ≫ j) ≫ b' := by
    rw [← Category.assoc, h0]
  have hrelb : (j ▷ J.{u}) ≫ (H ≫ b') = (fst K J.{u} ≫ j) ≫ b' := by
    rw [← Category.assoc, hrel]
  have hL : g0 ≫ p = (L ◁ zeroInclusion.{u}) ≫ bottom := by
    dsimp [g0, bottom]
    simp only [zero_whisker_endpoint, Category.assoc, hw, h0b]
  have hK : gK ≫ p = (j ▷ J.{u}) ≫ bottom := by
    dsimp [gK, bottom]
    simp only [Category.assoc, hw, hrelb]
  have ht : top ≫ p = sq.ι ≫ bottom := by
    apply sq.isPushout.hom_ext
    · rw [← Category.assoc, IsPushout.inl_desc, ← Category.assoc, sq.inl_ι]
      exact hL
    · rw [← Category.assoc, IsPushout.inr_desc, ← Category.assoc, sq.inr_ι]
      exact hK
  have : HasLiftingProperty sq.ι p := hp j sq
  let big : CommSq top sq.ι p bottom := ⟨ht⟩
  let g := intervalEndpoint L true ≫ big.lift
  have hg : g ≫ p = b' := by
    dsimp [g]
    rw [Category.assoc, big.fac_right]
    change intervalEndpoint L true ≫ (H ≫ b') = b'
    rw [← Category.assoc, h1, Category.id_comp]
  have htop : (j ▷ J.{u}) ≫ big.lift = gK := by
    have he : sq.inr ≫ sq.ι = j ▷ J.{u} := sq.inr_ι
    rw [← he, Category.assoc, big.fac_left]
    exact sq.isPushout.inr_desc g0 gK w
  have hjg : j ≫ g = a' := by
    have hn : j ≫ intervalEndpoint L true = intervalEndpoint K true ≫ (j ▷ J.{u}) := by
      apply NatTrans.ext
      rfl
    dsimp [g]
    rw [← Category.assoc, hn, Category.assoc, htop]
    apply NatTrans.ext
    rfl
  let k := factor g
  refine ⟨k, ?_, ?_⟩
  · apply (cancel_mono (ordinaryCoreCandidate E).ι).mp
    rw [Category.assoc, factor_comp]
    exact hjg
  · apply (cancel_mono (ordinaryCoreCandidate X).ι).mp
    rw [Category.assoc, ordinaryCoreCandidateMap_comp_ι, ← Category.assoc, factor_comp]
    exact hg

theorem core_fibration_of_relative_walking {E X : SSet.{u}}
    [E.Quasicategory] [X.Quasicategory] (p : E ⟶ X)
    (hp : ∀ {K L : SSet.{u}} (j : K ⟶ L) [Mono j]
      (sq : SSet.PushoutTensor j zeroInclusion.{u}), HasLiftingProperty sq.ι p) :
    Fibration (ordinaryCoreCandidateMap p) := by
  have : (ordinaryCoreCandidate E : SSet.{u}).KanComplex := native_quasi_core_kan E
  have : (ordinaryCoreCandidate X : SSet.{u}).KanComplex := native_quasi_core_kan X
  let d := MorphismProperty.factorizationData (trivialCofibrations SSet.{u})
    (fibrations SSet.{u}) (ordinaryCoreCandidateMap p)
  have : Cofibration d.i := (mem_trivialCofibrations_iff _).mp d.hi |>.1
  have : WeakEquivalence d.i := (mem_trivialCofibrations_iff _).mp d.hi |>.2
  have : Fibration d.p := (HomotopicalAlgebra.fibration_iff _).mpr d.hp
  have : d.Z.KanComplex := isFibrant_of_fibration d.p
  have : HasLiftingProperty d.i (ordinaryCoreCandidateMap p) := core_lifts_Kan_trivial p hp d.i
  exact (HomotopicalAlgebra.fibration_iff _).mpr
    ((fibrations SSet.{u}).of_retract (RetractArrow.ofRightLiftingProperty d.fac) d.hp)

theorem mono_restriction_core_fibration {A B : SSet.{u}} (i : A ⟶ B) [Mono i]
    (Z : SSet.{u}) [Z.Quasicategory] :
    Fibration (ordinaryCoreCandidateMap ((MonoidalClosed.pre i).app Z)) := by
  have : ((ihom A).obj Z).Quasicategory := ihom_quasicategory A Z
  have : ((ihom B).obj Z).Quasicategory := ihom_quasicategory B Z
  apply core_fibration_of_relative_walking
  intro K L j _ sq
  exact restriction_relative_zero_lifting i j Z sq

end
end DaggerNativeRelativeWalkingCoreFibration
