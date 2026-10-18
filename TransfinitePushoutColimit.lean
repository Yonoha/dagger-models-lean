import TransfinitePushoutDiagram
import Mathlib.CategoryTheory.Adjunction.Limits

set_option autoImplicit false
set_option maxHeartbeats 0
open CategoryTheory Limits

universe w v u
namespace DaggerTransfinitePushoutData
noncomputable section

variable {V : Type u} [Category.{v} V] {J : Type w}
  [LinearOrder J] [SuccOrder J] [OrderBot J] [WellFoundedLT J]
  {C B C' B' : V} {i : C ⟶ B} (h : TransfiniteCompositionOfShape J i)

@[reassoc (attr := simp)]
theorem sourceMap_incl (j : J) : sourceMap h j ≫ h.incl.app j = i := by
  have ht : h.F.map (homOfLE (bot_le : ⊥ ≤ j)) ≫ h.incl.app j = h.incl.app ⊥ :=
    (h.incl.naturality (homOfLE (bot_le : ⊥ ≤ j))).trans
      (Category.comp_id (show h.F.obj ⊥ ⟶ B from h.incl.app ⊥))
  calc
    sourceMap h j ≫ h.incl.app j =
        h.isoBot.inv ≫ (h.F.map (homOfLE (bot_le : ⊥ ≤ j)) ≫ h.incl.app j) :=
      Category.assoc _ _ _
    _ = h.isoBot.inv ≫ h.incl.app ⊥ := congrArg (fun t ↦ h.isoBot.inv ≫ t) ht
    _ = i := h.fac

def underCocone : Cocone (underDiagram h) :=
  Under.liftCocone h.F (sourceNat h) (Cocone.mk B h.incl) i (sourceMap_incl h)

def underIsColimit : IsColimit (underCocone h) :=
  Under.isColimitLiftCocone h.F (sourceNat h) (Cocone.mk B h.incl) i
    (sourceMap_incl h) h.isColimit

variable (F : C ⟶ C') [HasPushoutsAlong F]

def canonicalCocone : Cocone (diagram h F) :=
  (Under.forget C').mapCocone ((Under.pushout F).mapCocone (underCocone h))

def canonicalIsColimit : IsColimit (canonicalCocone h F) :=
  isColimitOfPreserves (Under.forget C')
    (isColimitOfPreserves (Under.pushout F) (underIsColimit h))

@[reassoc (attr := simp)]
theorem canonical_eta_leg (j : J) :
    (eta h F).app j ≫ (canonicalCocone h F).ι.app j = h.incl.app j ≫ pushout.inl i F := by
  change pushout.inl (sourceMap h j) F ≫ pushout.desc
    (h.incl.app j ≫ pushout.inl i F) (pushout.inr i F) _ = _
  exact pushout.inl_desc _ _ _

@[reassoc (attr := simp)]
theorem canonical_source_leg (j : J) :
    (sourceLeg h F).app j ≫ (canonicalCocone h F).ι.app j = pushout.inr i F := by
  change pushout.inr (sourceMap h j) F ≫ pushout.desc
    (h.incl.app j ≫ pushout.inl i F) (pushout.inr i F) _ = _
  exact pushout.inr_desc _ _ _

variable (f' : B ⟶ B') (i' : C' ⟶ B') (sq : IsPushout F i i' f')

def inclMap (j : J) : (diagram h F).obj j ⟶ B' :=
  (stageSquare h F j).desc (h.incl.app j ≫ f') i' (by
    rw [← Category.assoc, sourceMap_incl]
    exact sq.w.symm)

@[reassoc (attr := simp)]
theorem eta_inclMap (j : J) :
    (eta h F).app j ≫ inclMap h F f' i' sq j = h.incl.app j ≫ f' :=
  (stageSquare h F j).inl_desc _ _ _

@[reassoc (attr := simp)]
theorem sourceLeg_inclMap (j : J) :
    (sourceLeg h F).app j ≫ inclMap h F f' i' sq j = i' :=
  (stageSquare h F j).inr_desc _ _ _

def incl : diagram h F ⟶ (Functor.const J).obj B' where
  app := inclMap h F f' i' sq
  naturality j k t := by
    change (diagram h F).map t ≫ inclMap h F f' i' sq k =
      inclMap h F f' i' sq j ≫ 𝟙 B'
    rw [Category.comp_id]
    apply (stageSquare h F j).hom_ext
    · rw [eta_naturality_assoc, eta_inclMap, eta_inclMap]
      have ht : h.F.map t ≫ h.incl.app k = h.incl.app j :=
        (h.incl.naturality t).trans
          (Category.comp_id (show h.F.obj j ⟶ B from h.incl.app j))
      rw [← Category.assoc, ht]
    · rw [sourceLeg_naturality_assoc, sourceLeg_inclMap, sourceLeg_inclMap]

@[reassoc (attr := simp)]
theorem eta_incl (j : J) :
    (eta h F).app j ≫ (incl h F f' i' sq).app j = h.incl.app j ≫ f' :=
  eta_inclMap h F f' i' sq j

@[reassoc (attr := simp)]
theorem sourceLeg_incl (j : J) :
    (sourceLeg h F).app j ≫ (incl h F f' i' sq).app j = i' :=
  sourceLeg_inclMap h F f' i' sq j

def finalIso : (canonicalCocone h F).pt ≅ B' :=
  (IsPushout.of_hasPushout i F).isoIsPushout _ _ sq.flip

@[reassoc (attr := simp)]
theorem finalIso_left : pushout.inl i F ≫ (finalIso h F f' i' sq).hom = f' :=
  (IsPushout.of_hasPushout i F).inl_isoIsPushout_hom _ _ sq.flip

@[reassoc (attr := simp)]
theorem finalIso_right : pushout.inr i F ≫ (finalIso h F f' i' sq).hom = i' :=
  (IsPushout.of_hasPushout i F).inr_isoIsPushout_hom _ _ sq.flip

theorem canonical_leg (j : J) :
    (canonicalCocone h F).ι.app j ≫ (finalIso h F f' i' sq).hom =
      (incl h F f' i' sq).app j := by
  apply (stageSquare h F j).hom_ext
  · rw [canonical_eta_leg_assoc, finalIso_left, eta_incl]
  · rw [canonical_source_leg_assoc, finalIso_right, sourceLeg_incl]

def finalCocone : Cocone (diagram h F) := Cocone.mk B' (incl h F f' i' sq)

def finalIsColimit : IsColimit (finalCocone h F f' i' sq) :=
  IsColimit.ofIsoColimit (canonicalIsColimit h F)
    (Cocones.ext (finalIso h F f' i' sq) (canonical_leg h F f' i' sq))

def finalDesc (s : Cocone (diagram h F)) : B' ⟶ s.pt :=
  (finalIsColimit h F f' i' sq).desc s

@[reassoc (attr := simp)]
theorem finalDesc_fac (s : Cocone (diagram h F)) (j : J) :
    (incl h F f' i' sq).app j ≫ finalDesc h F f' i' sq s = s.ι.app j :=
  (finalIsColimit h F f' i' sq).fac s j

theorem finalDesc_uniq (s : Cocone (diagram h F)) (t : B' ⟶ s.pt)
    (ht : ∀ j, (incl h F f' i' sq).app j ≫ t = s.ι.app j) :
    t = finalDesc h F f' i' sq s := (finalIsColimit h F f' i' sq).uniq s t ht

omit f' i' sq in
def limitIsColimit (m : J) (hm : Order.IsSuccLimit m) :
    IsColimit ((Set.principalSegIio m).cocone (diagram h F)) := by
  letI : Nonempty (Set.Iio m) := ⟨⟨⊥, hm.bot_lt⟩⟩
  let r := (Set.principalSegIio m).monotone.functor
  let s : (Functor.const (Set.Iio m)).obj C ⟶ r ⋙ h.F :=
    Functor.whiskerLeft r (sourceNat h)
  let co := (Set.principalSegIio m).cocone h.F
  let hp : ∀ j, s.app j ≫ co.ι.app j = sourceMap h m :=
    fun j ↦ sourceMap_naturality h (homOfLE (le_of_lt j.2))
  let hc := Under.isColimitLiftCocone (r ⋙ h.F) s co (sourceMap h m) hp
    (h.F.isColimitOfIsWellOrderContinuous m hm)
  exact isColimitOfPreserves (Under.forget C') (isColimitOfPreserves (Under.pushout F) hc)

omit f' i' sq in
theorem diagram_isWellOrderContinuous : (diagram h F).IsWellOrderContinuous where
  nonempty_isColimit m hm := ⟨limitIsColimit h F m hm⟩

end
end DaggerTransfinitePushoutData
