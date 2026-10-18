import NativeJoyalFirstFactorization

/-!
# Recognition of weak right candidates by the original retract argument

Given a genuine C / C.rlp factorization and C.rlp contained in W, factor a weak
candidate f as i followed by p. Two-out-of-three makes i weak. The candidate lifts
against i, so f is an actual arrow retract of p and therefore belongs to C.rlp.
No model on the candidate classes or extra lifting hypothesis is supplied.
-/
set_option autoImplicit false
open CategoryTheory
universe v u
namespace DaggerNativeWeakRightRecognition
noncomputable section

theorem candidate_weak_le_rlp {E : Type u} [Category.{v} E]
    (C W : MorphismProperty E) [W.HasTwoOutOfThreeProperty]
    (d : C.FactorizationData C.rlp) (hR : C.rlp ≤ W) :
    (C ⊓ W).rlp ⊓ W ≤ C.rlp := by
  intro A B f hf
  let q := d f
  have hiW : W q.i := W.of_postcomp q.i q.p (hR q.p q.hp)
    (by rw [q.fac]; exact hf.2)
  haveI : HasLiftingProperty q.i f := hf.1 q.i ⟨q.hi, hiW⟩
  let sq : CommSq (𝟙 A) q.i f q.p := ⟨by rw [Category.id_comp, q.fac]⟩
  let r : RetractArrow f q.p :=
    { i := Arrow.homMk q.i (𝟙 B) (by
        change q.i ≫ q.p = f ≫ 𝟙 B
        rw [Category.comp_id, q.fac])
      r := Arrow.homMk sq.lift (𝟙 B) (by
        change sq.lift ≫ f = q.p ≫ 𝟙 B
        rw [Category.comp_id]
        exact sq.fac_right)
      retract := by ext <;> simp [sq.fac_left] }
  exact C.rlp.of_retract r q.hp

theorem candidate_weak_eq_rlp {E : Type u} [Category.{v} E]
    (C W : MorphismProperty E) [W.HasTwoOutOfThreeProperty]
    (d : C.FactorizationData C.rlp) (hR : C.rlp ≤ W) :
    (C ⊓ W).rlp ⊓ W = C.rlp := by
  apply le_antisymm
  · exact candidate_weak_le_rlp C W d hR
  · intro A B f hf
    exact ⟨MorphismProperty.antitone_rlp inf_le_left f hf, hR f hf⟩

end
end DaggerNativeWeakRightRecognition
