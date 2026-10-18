import ChallengeOverNerveFibre

/-!
# The strict fibre of the nerve of the native over-category forgetful functor

Use native functor congruence and equality-to-arrow transport to recover the
final arrow of a chain whose entire projection is the constant chain at X.
Every over object and every commuting triangle are retained. The resulting
constant chain is equal to the original chain, not merely isomorphic to it.
-/
set_option autoImplicit false
open CategoryTheory
universe u
namespace DaggerOriginalOverNerveFibreChallengeProof
noncomputable section

/-- Equality of original over objects retains both the source and the final arrow. -/
theorem overObject_eq {T : Type u} [Category.{u} T] {y : T} {a b : Over y}
    (h : a.left = b.left) (hh : HEq a.hom b.hom) : a = b := by
  rcases a with ⟨a, ⟨⟨⟩⟩, ha⟩
  rcases b with ⟨b, ⟨⟨⟩⟩, hb⟩
  dsimp at h
  subst b
  have he : ha = hb := eq_of_heq hh
  subst hb
  rfl

/-- Over morphisms agree when their endpoints and underlying maps agree. -/
theorem overHom_heq {T : Type u} [Category.{u} T] {y : T}
    {a b c d : Over y} (ha : a = c) (hb : b = d) (f : a ⟶ b) (g : c ⟶ d)
    (h : HEq f.left g.left) : HEq f g := by
  cases ha
  cases hb
  exact heq_of_eq (CostructuredArrow.ext f g (eq_of_heq h))

/-- Extract the original final arrow, transporting its source along the full projection. -/
def fibreArrow {T : Type u} [Category.{u} T] {x y : T} {n : ℕ}
    (A : Fin (n + 1) ⥤ Over y)
    (h : A ⋙ Over.forget y = (Functor.const (Fin (n + 1))).obj x) : x ⟶ y :=
  eqToHom (Functor.congr_obj h 0).symm ≫ (A.obj 0).hom

/-- Every vertex of a projected constant chain has the same transported final arrow. -/
theorem transportedFinalArrow_eq {T : Type u} [Category.{u} T] {x y : T} {n : ℕ}
    (A : Fin (n + 1) ⥤ Over y)
    (h : A ⋙ Over.forget y = (Functor.const (Fin (n + 1))).obj x)
    (i : Fin (n + 1)) :
    eqToHom (Functor.congr_obj h i).symm ≫ (A.obj i).hom = fibreArrow A h := by
  let e : (0 : Fin (n + 1)) ⟶ i := homOfLE (Fin.zero_le i)
  have hm : (A.map e).left =
      eqToHom (Functor.congr_obj h 0) ≫ eqToHom (Functor.congr_obj h i).symm := by
    simpa using Functor.congr_hom h e
  calc
    eqToHom (Functor.congr_obj h i).symm ≫ (A.obj i).hom =
        eqToHom (Functor.congr_obj h 0).symm ≫ (A.map e).left ≫ (A.obj i).hom := by
      rw [hm]
      simp
    _ = fibreArrow A h := by rw [Over.w]; rfl

/-- The entire original chain is the constant chain at the extracted original arrow. -/
theorem chain_eq_const {T : Type u} [Category.{u} T] {x y : T} {n : ℕ}
    (A : Fin (n + 1) ⥤ Over y)
    (h : A ⋙ Over.forget y = (Functor.const (Fin (n + 1))).obj x) :
    A = (Functor.const (Fin (n + 1))).obj (Over.mk (fibreArrow A h)) := by
  have hobj : ∀ i, A.obj i = Over.mk (fibreArrow A h) := by
    intro i
    apply overObject_eq (a := A.obj i) (b := Over.mk (fibreArrow A h))
      (Functor.congr_obj h i)
    exact (eqToHom_comp_heq (A.obj i).hom (Functor.congr_obj h i).symm).symm.trans
      (heq_of_eq (transportedFinalArrow_eq A h i))
  refine Functor.hext hobj ?_
  intro i j e
  apply overHom_heq (hobj i) (hobj j)
  exact (conj_eqToHom_iff_heq (A.map e).left (𝟙 x)
    (Functor.congr_obj h i) (Functor.congr_obj h j)).1 (Functor.congr_hom h e)

/-- The strict fibre contains exactly one constant chain for each original arrow. -/
theorem existsUniqueArrow {T : Type u} [Category.{u} T] {x y : T} {n : ℕ}
    (A : Fin (n + 1) ⥤ Over y)
    (h : A ⋙ Over.forget y = (Functor.const (Fin (n + 1))).obj x) :
    ∃! f : x ⟶ y, A = (Functor.const (Fin (n + 1))).obj (Over.mk f) := by
  refine ⟨fibreArrow A h, chain_eq_const A h, ?_⟩
  intro g hg
  have ho := (Functor.congr_obj hg 0).symm.trans (Functor.congr_obj (chain_eq_const A h) 0)
  have hs := congrArg (fun a : Over y ↦ (⟨a.left, a.hom⟩ : Σ z : T, z ⟶ y)) ho
  exact eq_of_heq (Sigma.mk.inj hs).2

/-- The Mathlib-only Challenge is proved with the exact original constant-chain statement. -/
theorem challengeProof : ChallengeOverNerveFibre.Statement.{u} := by
  intro T inst x y n A h
  exact existsUniqueArrow A h

end
end DaggerOriginalOverNerveFibreChallengeProof
