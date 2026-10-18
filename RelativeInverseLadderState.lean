import RelativeInverseSuccessorStage

/-! Actual stage states and a compatible successor, with unchanged chosen global data. -/
set_option autoImplicit false
open CategoryTheory Limits
open DaggerNativeJoyalWeakSimplexInverse DaggerRelativeInverseTrackedData
universe u v w
namespace DaggerRelativeInverseLadderState
noncomputable section
variable {C : Type w} [Category.{v} C] {J : Type u} [SmallCategory J]
  [HasColimitsOfShape J C] (R : C ⥤ SSet.{u}) [PreservesColimitsOfShape J R]
  {F : J ⥤ Arrow C} (c : Cocone F) (d : SimplexInverseData (R.map c.pt.hom))

structure State where
  start : J
  finish : J
  transition : start ⟶ finish
  witness : Tracked R c d transition

variable (κ : Cardinal.{u}) [Fact κ.IsRegular] [IsCardinalFiltered J κ]
  (hc : IsColimit c)
  (hX : ∀ j : J, IsCardinalPresentable (R.obj (F.obj j).left) κ ∧
    IsCardinalPresentable (R.obj (F.obj j).right) κ)

def initial (i : J) : State R c d := by
  have : IsCardinalPresentable (R.obj (F.obj i).left) κ := (hX i).1
  have : IsCardinalPresentable (R.obj (F.obj i).right) κ := (hX i).2
  let h := exists_tracked R c d κ hc i
  exact ⟨i, h.choose, h.choose_spec.choose, h.choose_spec.choose_spec.some⟩

theorem initial_start (i : J) : (initial R c d κ hc hX i).start = i := rfl

def extension (e : State R c d) :
    Σ (k : J) (q : e.finish ⟶ k),
      {f : Tracked R c d q // Compatible R c d e.witness f} := by
  have : IsCardinalPresentable (R.obj (F.obj e.start).left) κ := (hX e.start).1
  have : IsCardinalPresentable (R.obj (F.obj e.start).right) κ := (hX e.start).2
  have : IsCardinalPresentable (R.obj (F.obj e.finish).left) κ := (hX e.finish).1
  have : IsCardinalPresentable (R.obj (F.obj e.finish).right) κ := (hX e.finish).2
  let h := DaggerRelativeInverseSuccessorStage.exists_next R c d κ hc e.transition e.witness
  exact ⟨h.choose, h.choose_spec.choose, h.choose_spec.choose_spec.choose,
    h.choose_spec.choose_spec.choose_spec⟩

def next (e : State R c d) : State R c d :=
  ⟨e.finish, (extension R c d κ hc hX e).1, (extension R c d κ hc hX e).2.1,
    (extension R c d κ hc hX e).2.2.val⟩

theorem next_start (e : State R c d) : (next R c d κ hc hX e).start = e.finish := rfl

theorem next_compatible (e : State R c d) :
    Compatible R c d e.witness (next R c d κ hc hX e).witness :=
  (extension R c d κ hc hX e).2.2.property

end
end DaggerRelativeInverseLadderState
