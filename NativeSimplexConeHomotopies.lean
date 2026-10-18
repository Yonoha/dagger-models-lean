import NativeStandardSimplexContraction

/-! Two original simplex homotopies joining minimum-with-a-vertex to identity and constant. -/
set_option autoImplicit false
open CategoryTheory MonoidalCategory Simplicial Opposite
universe u
namespace DaggerNativeSimplexConeHomotopies
noncomputable section

def minimumFunctor (n : ℕ) (k : Fin (n + 1)) :
    ULift.{u} (Fin (n + 1)) ⥤ ULift.{u} (Fin (n + 1)) where
  obj x := ⟨min k x.down⟩
  map {x y} f := homOfLE (min_le_min_left k (show x ≤ y from leOfHom f))

def constantFunctor (n : ℕ) (k : Fin (n + 1)) :
    ULift.{u} (Fin (n + 1)) ⥤ ULift.{u} (Fin (n + 1)) :=
  (Functor.const _).obj ⟨k⟩

def minimumToIdentity (n : ℕ) (k : Fin (n + 1)) :
    minimumFunctor.{u} n k ⟶ 𝟭 _ where
  app x := homOfLE (min_le_right k x.down)
  naturality _ _ _ := Subsingleton.elim _ _

def minimumToConstant (n : ℕ) (k : Fin (n + 1)) :
    minimumFunctor.{u} n k ⟶ constantFunctor n k where
  app x := homOfLE (min_le_left k x.down)
  naturality _ _ _ := Subsingleton.elim _ _

def vertex (n : ℕ) (k : Fin (n + 1)) : (Δ[n] : SSet.{u}) _⦋0⦌ :=
  SSet.stdSimplex.obj₀Equiv.symm k

def minimumMap (n : ℕ) (k : Fin (n + 1)) : (Δ[n] : SSet.{u}) ⟶ Δ[n] :=
  (SSet.stdSimplex.isoNerve n).hom ≫ nerveMap (minimumFunctor n k) ≫
    (SSet.stdSimplex.isoNerve n).inv

def identityHomotopy (n : ℕ) (k : Fin (n + 1)) :
    SSet.Homotopy (minimumMap.{u} n k) (𝟙 _) :=
  ((DaggerNerveHomotopy.natTransHomotopy (minimumToIdentity n k)).precomp
      (SSet.stdSimplex.isoNerve n).hom).postcomp
      (SSet.stdSimplex.isoNerve n).inv |>.congr rfl (by
    have hn : nerveMap (𝟭 (ULift.{u} (Fin (n + 1)))) = 𝟙 _ := by
      apply NatTrans.ext
      funext d s
      exact Functor.comp_id s
    rw [hn, Category.comp_id, Iso.hom_inv_id])

def constantHomotopy (n : ℕ) (k : Fin (n + 1)) :
    SSet.Homotopy (minimumMap.{u} n k) (SSet.const (vertex n k)) :=
  ((DaggerNerveHomotopy.natTransHomotopy (minimumToConstant n k)).precomp
      (SSet.stdSimplex.isoNerve n).hom).postcomp
      (SSet.stdSimplex.isoNerve n).inv |>.congr rfl (by
    apply NatTrans.ext
    funext d s
    ext i
    rfl)

theorem identityHomotopy_vertex (n : ℕ) (k : Fin (n + 1)) (d : SimplexCategoryᵒᵖ)
    (s : (Δ[n] : SSet.{u}).obj d) (t : (Δ[1] : SSet.{u}).obj d)
    (r : Fin (d.unop.len + 1)) :
    SSet.stdSimplex.asOrderHom ((identityHomotopy n k).h.app d (s, t)) r =
      (if SSet.stdSimplex.asOrderHom t r = 0 then
        min k (SSet.stdSimplex.asOrderHom s r) else SSet.stdSimplex.asOrderHom s r) := by
  cases d with
  | op d =>
    induction d using SimplexCategory.rec with
    | h m =>
      dsimp [identityHomotopy, constantHomotopy, DaggerNerveHomotopy.natTransHomotopy,
        DaggerNerveHomotopy.natTransMap, SimplexCategory.toCat,
        SimplexCategory.skeletalFunctor]
      change ((Functor.uncurry.obj (ComposableArrows.mk₁ (minimumToIdentity.{u} n k))).obj
        (SSet.stdSimplex.asOrderHom t r, ULift.up (SSet.stdSimplex.asOrderHom s r))).down = _
      generalize SSet.stdSimplex.asOrderHom t r = q
      fin_cases q <;> rfl


theorem constantHomotopy_vertex (n : ℕ) (k : Fin (n + 1)) (d : SimplexCategoryᵒᵖ)
    (s : (Δ[n] : SSet.{u}).obj d) (t : (Δ[1] : SSet.{u}).obj d)
    (r : Fin (d.unop.len + 1)) :
    SSet.stdSimplex.asOrderHom ((constantHomotopy n k).h.app d (s, t)) r =
      (if SSet.stdSimplex.asOrderHom t r = 0 then
        min k (SSet.stdSimplex.asOrderHom s r) else k) := by
  cases d with
  | op d =>
    induction d using SimplexCategory.rec with
    | h m =>
      dsimp [identityHomotopy, constantHomotopy, DaggerNerveHomotopy.natTransHomotopy,
        DaggerNerveHomotopy.natTransMap, SimplexCategory.toCat,
        SimplexCategory.skeletalFunctor]
      change ((Functor.uncurry.obj (ComposableArrows.mk₁ (minimumToConstant.{u} n k))).obj
        (SSet.stdSimplex.asOrderHom t r, ULift.up (SSet.stdSimplex.asOrderHom s r))).down = _
      generalize SSet.stdSimplex.asOrderHom t r = q
      fin_cases q <;> rfl


end
end DaggerNativeSimplexConeHomotopies
