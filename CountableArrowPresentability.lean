import Mathlib.CategoryTheory.Presentable.Limits
import Mathlib.CategoryTheory.Functor.OfSequence

/-! Countable original Arrow colimits retain the common uncountable presentability rank. -/
set_option autoImplicit false
open CategoryTheory Limits
universe u v w
namespace DaggerCountableArrowPresentability

theorem nat_hasCardinalLT (κ : Cardinal.{u}) (hκ : Cardinal.aleph0 < κ) :
    HasCardinalLT ℕ κ := by
  have h : HasCardinalLT (ULift.{u} ℕ) κ := by
    rw [hasCardinalLT_iff_cardinal_mk_lt, Cardinal.mk_uLift, Cardinal.mk_nat,
      Cardinal.lift_aleph0]
    exact hκ
  exact (hasCardinalLT_ulift_iff _ _).1 h

theorem arrow_nat_hasCardinalLT (κ : Cardinal.{u}) (hκ : Cardinal.aleph0 < κ) :
    HasCardinalLT (Arrow ℕ) κ := by
  have hNat := nat_hasCardinalLT κ hκ
  have hPair : HasCardinalLT (ℕ × ℕ) κ := hasCardinalLT_prod hκ.le hNat hNat
  apply hPair.of_injective (fun a : Arrow ℕ ↦ (a.left, a.right))
  intro a b h
  apply Arrow.ext (congrArg Prod.fst h) (congrArg Prod.snd h)
  exact Subsingleton.elim _ _

theorem colimit_presentable {C : Type w} [Category.{v} C] [LocallySmall.{u} C]
    {F : ℕ ⥤ C} (c : Cocone F) (hc : IsColimit c)
    (κ : Cardinal.{u}) [Fact κ.IsRegular] (hκ : Cardinal.aleph0 < κ)
    [∀ n, IsCardinalPresentable (F.obj n) κ] : IsCardinalPresentable c.pt κ :=
  isCardinalPresentable_of_isColimit c hc κ (arrow_nat_hasCardinalLT κ hκ)

end DaggerCountableArrowPresentability
