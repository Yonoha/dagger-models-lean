import CountableArrowStageDiagrams
import RelativeArrowStageFacs

/-! The strictly coherent crossed inverses descend to the entire original colimit inverse. -/
set_option autoImplicit false
open CategoryTheory Limits
open DaggerRelativeInverseLadderData DaggerCountableArrowStageDiagrams
universe u v w
namespace DaggerCountableCrossedInverseColimit
noncomputable section
variable {C : Type w} [Category.{v} C] [HasColimitsOfShape ℕ C]
  (R : C ⥤ SSet.{u}) [PreservesColimitsOfShape ℕ R]
  {D : ℕ ⥤ Arrow C} (c : Cocone D) (e : Ladder R D)

def inverseCocone : Cocone (rightDiagram R (D := D)) where
  pt := R.obj c.pt.left
  ι := NatTrans.ofSequence (fun n ↦ (e.data n).inv ≫ R.map (c.ι.app (n + 1)).left) (by
    intro n
    change R.map (step D n).right ≫
      ((e.data (n + 1)).inv ≫ R.map (c.ι.app (n + 1 + 1)).left) =
        ((e.data n).inv ≫ R.map (c.ι.app (n + 1)).left) ≫ 𝟙 _
    rw [Category.comp_id, ← Category.assoc, e.inverse_compatible, Category.assoc, left_leg])

def inverse (hc : IsColimit c) : R.obj c.pt.right ⟶ R.obj c.pt.left :=
  (rightIsColimit R c hc).desc (inverseCocone R c e)

theorem inverse_fac (hc : IsColimit c) (n : ℕ) :
    R.map (c.ι.app n).right ≫ inverse R c e hc =
      (e.data n).inv ≫ R.map (c.ι.app (n + 1)).left :=
  (rightIsColimit R c hc).fac (inverseCocone R c e) n

theorem left_composite (hc : IsColimit c) (n : ℕ) :
    (R.map (D.obj n).hom ≫ (e.data n).inv) ≫ R.map (c.ι.app (n + 1)).left =
      R.map (c.ι.app n).left ≫ (R.map c.pt.hom ≫ inverse R c e hc) := by
  have h : R.map (c.ι.app n).left ≫ R.map c.pt.hom =
      R.map (D.obj n).hom ≫ R.map (c.ι.app n).right :=
    DaggerRelativeArrowStageFacs.map_square R (c.ι.app n)
  rw [Category.assoc, ← inverse_fac R c e hc n, ← Category.assoc, ← h, Category.assoc]

theorem right_composite (hc : IsColimit c) (n : ℕ) :
    ((e.data n).inv ≫ R.map (D.obj (n + 1)).hom) ≫ R.map (c.ι.app (n + 1)).right =
      R.map (c.ι.app n).right ≫ (inverse R c e hc ≫ R.map c.pt.hom) := by
  have h : R.map (c.ι.app (n + 1)).left ≫ R.map c.pt.hom =
      R.map (D.obj (n + 1)).hom ≫ R.map (c.ι.app (n + 1)).right :=
    DaggerRelativeArrowStageFacs.map_square R (c.ι.app (n + 1))
  rw [Category.assoc, ← h, ← Category.assoc, ← inverse_fac R c e hc n, Category.assoc]

end
end DaggerCountableCrossedInverseColimit
