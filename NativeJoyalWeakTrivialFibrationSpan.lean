import NativeOriginalSecondFactorization
import NativeJoyalTrivialRecognition
import NativeWeakMonoQuasicategoryExtension
import NativeInnerQuasicategoryWeakReplacement

/-! A weak map of original quasi-categories has a span of actual mono-right maps. -/
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open DaggerNativeJoyalMappingTest DaggerNativeJoyalFirstFactorization
open DaggerNativeWeakMonoQuasicategoryExtension
open DaggerNativeJoyalTrivialRecognition DaggerNativeOriginalSecondFactorization
universe u
namespace DaggerNativeJoyalWeakTrivialFibrationSpan
noncomputable section

local instance candidateComp : candidateFibrations.{u}.IsStableUnderComposition := by
  unfold candidateFibrations
  infer_instance

theorem terminal_candidate (X : SSet.{u}) [X.Quasicategory] :
    candidateFibrations (terminal.from X) := by
  intro A B i hi
  have : Mono i := hi.1
  exact weak_mono_terminal_lifting i hi.2 X

theorem fst_candidate (X Y : SSet.{u}) [Y.Quasicategory] :
    candidateFibrations (fst X Y) := by
  intro A B i hi
  have : Mono i := hi.1
  constructor
  intro a b sq
  obtain ⟨e, he⟩ := weak_mono_extension i hi.2 Y (a ≫ snd X Y)
  let l : B ⟶ X ⊗ Y :=
    { app := fun q z ↦ (b.app q z, e.app q z)
      naturality := by
        intro q r α
        funext z
        exact Prod.ext (congrFun (b.naturality α) z)
          (congrFun (e.naturality α) z) }
  refine ⟨l, ?_, ?_⟩
  · apply NatTrans.ext
    funext q z
    apply Prod.ext
    · exact (congrFun (NatTrans.congr_app sq.w q) z).symm
    · exact congrFun (NatTrans.congr_app he q) z
  · rfl

theorem snd_candidate (X Y : SSet.{u}) [X.Quasicategory] :
    candidateFibrations (snd X Y) := by
  intro A B i hi
  have : Mono i := hi.1
  constructor
  intro a b sq
  obtain ⟨e, he⟩ := weak_mono_extension i hi.2 X (a ≫ fst X Y)
  let l : B ⟶ X ⊗ Y :=
    { app := fun q z ↦ (e.app q z, b.app q z)
      naturality := by
        intro q r α
        funext z
        exact Prod.ext (congrFun (e.naturality α) z)
          (congrFun (b.naturality α) z) }
  refine ⟨l, ?_, ?_⟩
  · apply NatTrans.ext
    funext q z
    apply Prod.ext
    · exact congrFun (NatTrans.congr_app he q) z
    · exact (congrFun (NatTrans.congr_app sq.w q) z).symm
  · rfl

structure Span {X Y : SSet.{u}} (f : X ⟶ Y) where
  middle : SSet.{u}
  quasi : middle.Quasicategory
  inclusion : X ⟶ middle
  left : middle ⟶ X
  right : middle ⟶ Y
  inclusion_left : inclusion ≫ left = 𝟙 X
  inclusion_right : inclusion ≫ right = f
  left_mono_rlp : (MorphismProperty.monomorphisms SSet.{u}).rlp left
  right_mono_rlp : (MorphismProperty.monomorphisms SSet.{u}).rlp right

def fromWeak {X Y : SSet.{u}} [X.Quasicategory] [Y.Quasicategory]
    (f : X ⟶ Y) (hf : weakCategoricalEquivalences f) : Span f := by
  let graph : X ⟶ X ⊗ Y :=
    { app := fun q z ↦ (z, f.app q z)
      naturality := by
        intro q r α
        funext z
        exact Prod.ext rfl (congrFun (f.naturality α) z) }
  let d := secondFactorization.factorizationData graph
  let l := d.p ≫ fst X Y
  let r := d.p ≫ snd X Y
  have hl : d.i ≫ l = 𝟙 X := by
    dsimp [l]
    rw [← Category.assoc, d.fac]
    rfl
  have hr : d.i ≫ r = f := by
    dsimp [r]
    rw [← Category.assoc, d.fac]
    rfl
  have hc : candidateFibrations l :=
    candidateFibrations.comp_mem d.p (fst X Y) d.hp (fst_candidate X Y)
  have hd : candidateFibrations r :=
    candidateFibrations.comp_mem d.p (snd X Y) d.hp (snd_candidate X Y)
  have hlw : weakCategoricalEquivalences l :=
    weakCategoricalEquivalences.of_precomp d.i l d.hi.2
      (hl.symm ▸ weakCategoricalEquivalences.id_mem X)
  have hrw : weakCategoricalEquivalences r :=
    weakCategoricalEquivalences.of_precomp d.i r d.hi.2 (hr.symm ▸ hf)
  have hz : d.Z.Quasicategory :=
    DaggerNativeInnerQuasicategoryWeakReplacement.candidate_terminal_quasicategory
      (l ≫ terminal.from X) terminalIsTerminal
      (candidateFibrations.comp_mem l (terminal.from X) hc (terminal_candidate X))
  exact ⟨d.Z, hz, d.i, l, r, hl, hr,
    candidate_trivial_le_mono_rlp l ⟨hc, hlw⟩,
    candidate_trivial_le_mono_rlp r ⟨hd, hrw⟩⟩

end
end DaggerNativeJoyalWeakTrivialFibrationSpan
