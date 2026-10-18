import NativeBisimplicialBoxYoneda
import NativeBisimplicialBoxIso

/-! The diagonal restriction bijection holds for every original simplex face. -/
set_option autoImplicit false
open CategoryTheory Simplicial Opposite
open DaggerNativeBisimplicialHorizontalMapping DaggerNativeBisimplicialBox
open DaggerNativeBisimplicialDiagonal DaggerNativeBisimplicialBoxYoneda
open DaggerNativeBisimplicialBoxIso
universe u
namespace DaggerNativeFaceBoxDiagonalEquivalence
noncomputable section

def boxDiagonalUnit (K : SSet.{u}) : K ⟶ diagonalFunctor.obj (box K K) where
  app _ a := (a, a)
  naturality _ _ _ := rfl

def boxRestriction (K : SSet.{u}) (X : BiSSet.{u}) (f : box K K ⟶ X) :
    K ⟶ diagonalFunctor.obj X := boxDiagonalUnit K ≫ diagonalFunctor.map f

theorem boxRestriction_pre {K L : SSet.{u}} (i : K ⟶ L) (X : BiSSet.{u})
    (f : box L L ⟶ X) :
    boxRestriction K X (boxMap i i ≫ f) = i ≫ boxRestriction L X f := by
  apply NatTrans.ext
  rfl

theorem boxRestriction_post (K : SSet.{u}) {X Y : BiSSet.{u}} (g : X ⟶ Y)
    (f : box K K ⟶ X) :
    boxRestriction K Y (f ≫ g) = boxRestriction K X f ≫ diagonalFunctor.map g := by
  apply NatTrans.ext
  rfl

theorem boxRestriction_bijective_of_iso {K : SSet.{u}} {n : ℕ} (e : Δ[n] ≅ K)
    (X : BiSSet.{u}) : Function.Bijective (boxRestriction K X) := by
  constructor
  · intro f g hfg
    apply (cancel_epi (boxIso e e).hom).mp
    apply (simplexRestriction_bijective n X).injective
    change boxRestriction (Δ[n] : SSet.{u}) X (boxMap e.hom e.hom ≫ f) =
      boxRestriction (Δ[n] : SSet.{u}) X (boxMap e.hom e.hom ≫ g)
    rw [boxRestriction_pre, boxRestriction_pre, hfg]
  · intro a
    refine ⟨boxMap e.inv e.inv ≫ simplexExtension n X (e.hom ≫ a), ?_⟩
    rw [boxRestriction_pre]
    change e.inv ≫ simplexRestriction n X (simplexExtension n X (e.hom ≫ a)) = a
    rw [simplexExtension_restrict, ← Category.assoc, e.inv_hom_id, Category.id_comp]

theorem empty_face_elim {n : ℕ} (h : SimplexCategoryᵒᵖ)
    (x : (SSet.stdSimplex.face (∅ : Finset (Fin (n + 1))) : SSet.{u}).obj h) : False := by
  cases h with
  | op h =>
    induction h using SimplexCategory.rec with
    | h m =>
      exact Finset.notMem_empty _ ((SSet.stdSimplex.mem_face_iff ∅ x.val).mp x.property 0)

theorem faceBoxRestriction_bijective {n : ℕ} (S : Finset (Fin (n + 1)))
    (X : BiSSet.{u}) :
    Function.Bijective (boxRestriction (SSet.stdSimplex.face S : SSet.{u}) X) := by
  classical
  by_cases hS : S = ∅
  · subst S
    constructor
    · intro f g _
      apply NatTrans.ext
      funext h
      apply NatTrans.ext
      funext v p
      exact (empty_face_elim h p.1).elim
    · intro a
      let f : box (SSet.stdSimplex.face (∅ : Finset (Fin (n + 1))) : SSet.{u})
          (SSet.stdSimplex.face (∅ : Finset (Fin (n + 1))) : SSet.{u}) ⟶ X :=
        { app := fun h ↦
            { app := fun _ p ↦ (empty_face_elim h p.1).elim
              naturality := by intros; funext p; exact (empty_face_elim _ p.1).elim }
          naturality := by
            intros
            apply NatTrans.ext
            funext v p
            exact (empty_face_elim _ p.1).elim }
      refine ⟨f, ?_⟩
      apply NatTrans.ext
      funext h x
      exact (empty_face_elim h x).elim
  · have hc : 0 < S.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hS)
    obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hc)
    exact boxRestriction_bijective_of_iso
      (SSet.stdSimplex.isoOfRepresentableBy
        (SSet.stdSimplex.faceRepresentableBy S m (S.orderIsoOfFin hm))) X

def faceBoxExtension {n : ℕ} (S : Finset (Fin (n + 1))) (X : BiSSet.{u})
    (a : (SSet.stdSimplex.face S : SSet.{u}) ⟶ diagonalFunctor.obj X) :
    box (SSet.stdSimplex.face S : SSet.{u}) (SSet.stdSimplex.face S : SSet.{u}) ⟶ X :=
  (Equiv.ofBijective _ (faceBoxRestriction_bijective S X)).symm a

theorem faceBoxExtension_restrict {n : ℕ} (S : Finset (Fin (n + 1))) (X : BiSSet.{u})
    (a : (SSet.stdSimplex.face S : SSet.{u}) ⟶ diagonalFunctor.obj X) :
    boxRestriction _ X (faceBoxExtension S X a) = a :=
  (Equiv.ofBijective _ (faceBoxRestriction_bijective S X)).apply_symm_apply a

end
end DaggerNativeFaceBoxDiagonalEquivalence
