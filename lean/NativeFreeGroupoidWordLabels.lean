import NativeSignedPathWords
import Mathlib.CategoryTheory.SingleObj

/-! A native free-groupoid functor records the entire signed edge word in a native free group. -/
set_option autoImplicit false
open CategoryTheory
open DaggerNativeSignedPathWords
universe u
namespace DaggerNativeFreeGroupoidWordLabels
noncomputable section

variable (V : Type u) [Quiver.{u + 1} V]

def labelPrefunctor : V ⥤q SingleObj (FreeGroup (Edge V)) where
  obj _ := SingleObj.star _
  map {a b} e := FreeGroup.of ⟨a, b, e⟩

def labelFunctor : Quiver.FreeGroupoid V ⥤ SingleObj (FreeGroup (Edge V)) :=
  Quiver.FreeGroupoid.lift (labelPrefunctor V)

def quotientMap : Paths (Quiver.Symmetrify V) ⥤ Quiver.FreeGroupoid V :=
  CategoryTheory.Quotient.functor Quiver.FreeGroupoid.redStep

theorem label_symmetric_path {a b : Quiver.Symmetrify V} (p : Quiver.Path a b) :
    (Paths.lift (Quiver.Symmetrify.lift (labelPrefunctor V))).map p =
      FreeGroup.mk (word p) := by
  induction p with
  | nil => exact FreeGroup.one_eq_mk
  | @cons b c p e ih =>
    rw [Paths.lift_cons, ih]
    cases e with
    | inl e =>
      change FreeGroup.mk [(⟨b, c, e⟩, true)] * FreeGroup.mk (word p) =
        FreeGroup.mk ((⟨b, c, e⟩, true) :: word p)
      exact FreeGroup.mul_mk
    | inr e =>
      change FreeGroup.mk [(⟨c, b, e⟩, false)] * FreeGroup.mk (word p) =
        FreeGroup.mk ((⟨c, b, e⟩, false) :: word p)
      exact FreeGroup.mul_mk

theorem label_quotient_path {a b : Quiver.Symmetrify V} (p : Quiver.Path a b) :
    (labelFunctor V).map ((quotientMap V).map p) = FreeGroup.mk (word p) :=
  label_symmetric_path V p

theorem reduced_paths_equal_of_quotient_eq {a b : Quiver.Symmetrify V}
    (p q : Quiver.Path a b) (hp : FreeGroup.IsReduced (word p))
    (hq : FreeGroup.IsReduced (word q))
    (he : (quotientMap V).map p = (quotientMap V).map q) : p = q := by
  have hl := congrArg (fun f ↦ (labelFunctor V).map f) he
  have hl' : FreeGroup.mk (word p) = FreeGroup.mk (word q) :=
    (label_quotient_path V p).symm.trans (hl.trans (label_quotient_path V q))
  obtain ⟨w, hpw, hqw⟩ := FreeGroup.Red.exact.mp hl'
  have hp' : w = word p := hp.red_iff_eq.mp hpw
  have hq' : w = word q := hq.red_iff_eq.mp hqw
  exact word_injective (hp'.symm.trans hq')

end
end DaggerNativeFreeGroupoidWordLabels
