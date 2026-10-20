import OriginalTaggedReverseFreeCompletion
import Mathlib.AlgebraicTopology.SimplicialSet.Boundary

/-!
# A concrete two-copy free anti-involutive simplicial set

The second copy has its simplicial operators reversed. Reversal swaps the
copies, including in degree zero. The eventual comparison with the original
left Kan extension uses uniqueness of the left adjoint to `antiForget`.
-/

set_option autoImplicit false

open CategoryTheory Simplicial Opposite

universe u

namespace DaggerModels.OriginalAntiInvolutiveFreePair

open DaggerModels.AntiInvolutiveSSet
open DaggerModels.OriginalTaggedReverseFreeCompletion

/-- Two disjoint simplex copies; the second uses the reversed operators. -/
def pairSSet (A : SSet.{u}) : SSet.{u} where
  obj n := A.obj n × Bool
  map {_ _} f p :=
    (A.map (if p.2 then (SimplexCategory.rev.map f.unop).op else f) p.1, p.2)
  map_id n := by
    funext p
    rcases p with ⟨x, b⟩
    cases b <;> simp
  map_comp f g := by
    funext p
    rcases p with ⟨x, b⟩
    cases b
    · change (A.map (f ≫ g) x, false) = (A.map g (A.map f x), false)
      rw [A.map_comp]
      rfl
    · change (A.map (SimplexCategory.rev.map (g.unop ≫ f.unop)).op x, true) =
          (A.map (SimplexCategory.rev.map g.unop).op
            (A.map (SimplexCategory.rev.map f.unop).op x), true)
      rw [Functor.map_comp, op_comp, A.map_comp]
      rfl

/-- Reversal exchanges the two copies at each simplicial degree. -/
def pairDagger (A : SSet.{u}) : pairSSet A ⟶ (pairSSet A).op where
  app _ p := (p.1, !p.2)
  naturality := by
    intro n m f
    funext p
    rcases p with ⟨x, b⟩
    cases b
    · change (A.map f x, true) =
          (A.map (SimplexCategory.rev.map
            (SimplexCategory.rev.map f.unop)).op x, true)
      rw [SimplexCategory.rev_map_rev_map]
      rfl
    · change (A.map (SimplexCategory.rev.map f.unop).op x, false) =
          (A.map (SimplexCategory.rev.map f.unop).op x, false)
      rfl

/-- The explicit object has a free reversal even at vertices. -/
def pairObj (A : SSet.{u}) : AntiInvolutiveSSet.{u} where
  toSSet := pairSSet A
  dagger := pairDagger A
  involutive _ p := by
    rcases p with ⟨x, b⟩
    cases b <;> rfl

/-- The simplex map acts identically on the Bool tag. -/
def pairMap {A B : SSet.{u}} (f : A ⟶ B) : pairObj A ⟶ pairObj B where
  hom :=
    { app := fun n p ↦ (f.app n p.1, p.2)
      naturality := by
        intro n m g
        funext p
        rcases p with ⟨x, b⟩
        cases b
        · change (f.app m (A.map g x), false) =
              (B.map g (f.app n x), false)
          exact Prod.ext (congrFun (f.naturality g) x) rfl
        · change (f.app m (A.map (SimplexCategory.rev.map g.unop).op x), true) =
              (B.map (SimplexCategory.rev.map g.unop).op (f.app n x), true)
          exact Prod.ext
            (congrFun (f.naturality (SimplexCategory.rev.map g.unop).op) x) rfl }
  comm := by
    ext n p
    rfl

/-- The concrete two-copy construction is functorial. -/
def pairFunctor : SSet.{u} ⥤ AntiInvolutiveSSet.{u} where
  obj := pairObj
  map := pairMap
  map_id A := by
    apply AntiInvolutiveSSet.Hom.ext
    ext n p
    rfl
  map_comp f g := by
    apply AntiInvolutiveSSet.Hom.ext
    ext n p
    rfl

/-- The ordinary simplex copy is the unit of the explicit free construction. -/
def first (A : SSet.{u}) : A ⟶ (pairObj A).toSSet where
  app _ x := (x, false)
  naturality := by
    intro n m g
    funext x
    rfl

private theorem dagger_app_involutive (Y : AntiInvolutiveSSet.{u})
    (n : SimplexCategoryᵒᵖ) (x : Y.toSSet.obj n) :
    Y.dagger.app n (Y.dagger.app n x) = x := by
  cases n with
  | op n =>
      induction n using SimplexCategory.rec with
      | h k => exact Y.involutive k x

/-- Extend a simplicial map over the second copy by the target reversal. -/
def extend {A : SSet.{u}} {Y : AntiInvolutiveSSet.{u}}
    (f : A ⟶ Y.toSSet) : pairObj A ⟶ Y where
  hom :=
    { app := fun n p ↦ if p.2 then Y.dagger.app n (f.app n p.1) else f.app n p.1
      naturality := by
        intro n m g
        funext p
        rcases p with ⟨x, b⟩
        cases b
        · change f.app m (A.map g x) = Y.toSSet.map g (f.app n x)
          exact congrFun (f.naturality g) x
        · change Y.dagger.app m
              (f.app m (A.map (SimplexCategory.rev.map g.unop).op x)) =
              Y.toSSet.map g (Y.dagger.app n (f.app n x))
          have h₁ := congrFun (f.naturality
            (SimplexCategory.rev.map g.unop).op) x
          change f.app m (A.map (SimplexCategory.rev.map g.unop).op x) =
            Y.toSSet.map (SimplexCategory.rev.map g.unop).op (f.app n x) at h₁
          rw [h₁]
          have h₂ := congrFun (Y.dagger.naturality
            (SimplexCategory.rev.map g.unop).op) (f.app n x)
          change Y.dagger.app m
              (Y.toSSet.map (SimplexCategory.rev.map g.unop).op (f.app n x)) =
              Y.toSSet.op.map (SimplexCategory.rev.map g.unop).op
                (Y.dagger.app n (f.app n x)) at h₂
          simpa [SSet.op_map, SSet.opObjEquiv,
            SimplexCategory.rev_map_rev_map] using h₂ }
  comm := by
    ext n p
    rcases p with ⟨x, b⟩
    cases b
    · rfl
    · exact dagger_app_involutive Y n (f.app n x)

/-- The explicit extension restricts to the original map on the first copy. -/
theorem first_extend {A : SSet.{u}} {Y : AntiInvolutiveSSet.{u}}
    (f : A ⟶ Y.toSSet) : first A ≫ (extend f).hom = f := by
  ext n x
  rfl

/-- Reversal forces the value on the second copy. -/
theorem second_forced {A : SSet.{u}} {Y : AntiInvolutiveSSet.{u}}
    (g : pairObj A ⟶ Y) (n : SimplexCategoryᵒᵖ) (x : A.obj n) :
    g.hom.app n (x, true) = Y.dagger.app n (g.hom.app n (x, false)) := by
  have h := congrFun (NatTrans.congr_app g.comm n) (x, false)
  exact h.symm

/-- Maps from the explicit free pair are exactly maps of underlying simplicial sets. -/
def homEquiv (A : SSet.{u}) (Y : AntiInvolutiveSSet.{u}) :
    (pairObj A ⟶ Y) ≃ (A ⟶ Y.toSSet) where
  toFun g := first A ≫ g.hom
  invFun := extend
  left_inv g := by
    apply AntiInvolutiveSSet.Hom.ext
    ext n p
    rcases p with ⟨x, b⟩
    cases b
    · rfl
    · exact (second_forced g n x).symm
  right_inv f := first_extend f

/-- The explicit two-copy functor is left adjoint to the original forgetful functor. -/
def pairAdjunction : pairFunctor.{u} ⊣ antiForget.{u} :=
  Adjunction.mkOfHomEquiv
    { homEquiv := homEquiv
      homEquiv_naturality_left_symm := fun {A B Y} f g ↦ by
        apply (homEquiv A Y).injective
        ext n x
        rfl
      homEquiv_naturality_right := fun {A Y Z} g h ↦ by
        ext n x
        rfl }

/-- The explicit pair and the literal tagged left Kan extension agree naturally. -/
noncomputable def pairIsoFreeAnti : pairFunctor.{u} ≅ freeAnti.{u} :=
  Adjunction.leftAdjointUniq pairAdjunction freeAntiAdjunction

end DaggerModels.OriginalAntiInvolutiveFreePair
