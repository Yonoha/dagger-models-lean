import DaggerModels.TypeFunctorPullback
import Mathlib.CategoryTheory.Limits.FilteredColimitCommutesFiniteLimit
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks

/-!
# Filtered colimits of literal Type-valued pullbacks

The componentwise fiber product is `DaggerModels.TypeFunctorPullback.functor`.
This file transports its pullback universal property through the filtered
colimit functor and identifies the result with a fiber product of specified
colimit cocones.
-/

open CategoryTheory Limits

universe u

namespace DaggerModels.OriginalFilteredPullbackColimit

variable {J : Type u} [SmallCategory J]
variable {F G H : J ⥤ Type u} (p : F ⟶ H) (q : G ⟶ H)
variable (cF : Cocone F) (cG : Cocone G) (cH : Cocone H)
variable (hF : IsColimit cF) (hG : IsColimit cG) (hH : IsColimit cH)
variable (p0 : cF.pt ⟶ cH.pt) (q0 : cG.pt ⟶ cH.pt)
variable (hp : ∀ j, cF.ι.app j ≫ p0 = p.app j ≫ cH.ι.app j)
variable (hq : ∀ j, cG.ι.app j ≫ q0 = q.app j ≫ cH.ι.app j)

/-- The literal fiber product of two maps of types. -/
abbrev Fiber {X Y Z : Type u} (p0 : X ⟶ Z) (q0 : Y ⟶ Z) : Type u :=
  {e : X × Y // p0 e.1 = q0 e.2}

/-- The componentwise cocone into the specified fiber product. -/
def cocone : Cocone (TypeFunctorPullback.functor p q) where
  pt := Fiber p0 q0
  ι := {
    app j e := ⟨(cF.ι.app j e.1.1, cG.ι.app j e.1.2), by
      calc
        p0 (cF.ι.app j e.1.1) = cH.ι.app j (p.app j e.1.1) :=
          congrFun (hp j) e.1.1
        _ = cH.ι.app j (q.app j e.1.2) := congrArg (cH.ι.app j) e.2
        _ = q0 (cG.ι.app j e.1.2) := (congrFun (hq j) e.1.2).symm⟩
    naturality := by
      intro i j f
      funext e
      apply Subtype.ext
      apply Prod.ext
      · simpa [TypeFunctorPullback.functor] using congrFun (cF.w f) e.1.1
      · simpa [TypeFunctorPullback.functor] using congrFun (cG.w f) e.1.2 }

private noncomputable def isoF : colimit F ≅ cF.pt :=
  (colimit.isColimit F).coconePointUniqueUpToIso hF

private noncomputable def isoG : colimit G ≅ cG.pt :=
  (colimit.isColimit G).coconePointUniqueUpToIso hG

private noncomputable def isoH : colimit H ≅ cH.pt :=
  (colimit.isColimit H).coconePointUniqueUpToIso hH

include hp in
private theorem map_p_compat :
    colim.map p ≫ (isoH cH hH).hom = (isoF cF hF).hom ≫ p0 := by
  apply (colimit.isColimit F).hom_ext
  intro j
  calc
    colimit.ι F j ≫ (colim.map p ≫ (isoH cH hH).hom) =
        p.app j ≫ (colimit.ι H j ≫ (isoH cH hH).hom) := by
      simp only [← Category.assoc, colimit.ι_map]
    _ = p.app j ≫ cH.ι.app j := by simp [isoH]
    _ = cF.ι.app j ≫ p0 := (hp j).symm
    _ = colimit.ι F j ≫ ((isoF cF hF).hom ≫ p0) := by
      simp [isoF]

include hq in
private theorem map_q_compat :
    colim.map q ≫ (isoH cH hH).hom = (isoG cG hG).hom ≫ q0 := by
  apply (colimit.isColimit G).hom_ext
  intro j
  calc
    colimit.ι G j ≫ (colim.map q ≫ (isoH cH hH).hom) =
        q.app j ≫ (colimit.ι H j ≫ (isoH cH hH).hom) := by
      simp only [← Category.assoc, colimit.ι_map]
    _ = q.app j ≫ cH.ι.app j := by simp [isoH]
    _ = cG.ι.app j ≫ q0 := (hq j).symm
    _ = colimit.ι G j ≫ ((isoG cG hG).hom ≫ q0) := by
      simp [isoG]

include hF hG hH hp hq in
private noncomputable def targetEquiv :
    Types.PullbackObj (colim.map p) (colim.map q) ≃ Fiber p0 q0 where
  toFun e := ⟨((isoF cF hF).hom e.1.1, (isoG cG hG).hom e.1.2), by
    calc
      p0 ((isoF cF hF).hom e.1.1) =
          (isoH cH hH).hom ((colim.map p) e.1.1) :=
        (congrFun (map_p_compat p cF cH hF hH p0 hp) e.1.1).symm
      _ = (isoH cH hH).hom ((colim.map q) e.1.2) :=
        congrArg (isoH cH hH).hom e.2
      _ = q0 ((isoG cG hG).hom e.1.2) :=
        congrFun (map_q_compat q cG cH hG hH q0 hq) e.1.2⟩
  invFun e := ⟨((isoF cF hF).inv e.1.1, (isoG cG hG).inv e.1.2), by
    apply ((isIso_iff_bijective (isoH cH hH).hom).mp inferInstance).1
    calc
      (isoH cH hH).hom ((colim.map p) ((isoF cF hF).inv e.1.1)) =
          p0 ((isoF cF hF).hom ((isoF cF hF).inv e.1.1)) :=
        congrFun (map_p_compat p cF cH hF hH p0 hp) _
      _ = p0 e.1.1 := by simp
      _ = q0 e.1.2 := e.2
      _ = q0 ((isoG cG hG).hom ((isoG cG hG).inv e.1.2)) := by simp
      _ = (isoH cH hH).hom ((colim.map q) ((isoG cG hG).inv e.1.2)) :=
        (congrFun (map_q_compat q cG cH hG hH q0 hq) _).symm⟩
  left_inv e := by
    apply Subtype.ext
    apply Prod.ext <;> simp
  right_inv e := by
    apply Subtype.ext
    apply Prod.ext <;> simp

variable [IsFiltered J]

include hF hG hH hp hq in
private noncomputable def comparisonEquiv :
    colimit (TypeFunctorPullback.functor p q) ≃ Fiber p0 q0 := by
  letI : PreservesLimitsOfShape WalkingCospan
      (colim : (J ⥤ Type u) ⥤ Type u) := inferInstance
  let hc := ((TypeFunctorPullback.cone p q).isLimitMapConeEquiv
    (colim : (J ⥤ Type u) ⥤ Type u)).1
      (isLimitOfPreserves (colim : (J ⥤ Type u) ⥤ Type u)
        (TypeFunctorPullback.isLimit p q))
  exact (PullbackCone.IsLimit.equivPullbackObj hc).trans
    (targetEquiv p q cF cG cH hF hG hH p0 q0 hp hq)

include hF hG hH in
/-- The literal componentwise pullback cocone is colimiting. -/
noncomputable def isColimit : IsColimit (cocone p q cF cG cH p0 q0 hp hq) := by
  let e := comparisonEquiv p q cF cG cH hF hG hH p0 q0 hp hq
  apply IsColimit.ofIsoColimit (colimit.isColimit (TypeFunctorPullback.functor p q))
  refine Cocones.ext e.toIso ?_
  intro j
  funext x
  apply Subtype.ext
  apply Prod.ext
  · change (e (colimit.ι (TypeFunctorPullback.functor p q) j x)).1.1 =
        cF.ι.app j x.1.1
    simp only [e, comparisonEquiv, Equiv.trans_apply, targetEquiv]
    change (isoF cF hF).hom
      ((colim.map (TypeFunctorPullback.fst p q))
        (colimit.ι (TypeFunctorPullback.functor p q) j x)) = cF.ι.app j x.1.1
    have h := congrFun (colimit.ι_map (TypeFunctorPullback.fst p q) j) x
    have h' : (colim.map (TypeFunctorPullback.fst p q))
        (colimit.ι (TypeFunctorPullback.functor p q) j x) =
        colimit.ι F j ((TypeFunctorPullback.fst p q).app j x) := by
      simpa only [types_comp_apply] using h
    rw [h']
    simpa [isoF, TypeFunctorPullback.fst] using
      congrFun (IsColimit.comp_coconePointUniqueUpToIso_hom
        (colimit.isColimit F) hF j) ((TypeFunctorPullback.fst p q).app j x)
  · change (e (colimit.ι (TypeFunctorPullback.functor p q) j x)).1.2 =
        cG.ι.app j x.1.2
    simp only [e, comparisonEquiv, Equiv.trans_apply, targetEquiv]
    change (isoG cG hG).hom
      ((colim.map (TypeFunctorPullback.snd p q))
        (colimit.ι (TypeFunctorPullback.functor p q) j x)) = cG.ι.app j x.1.2
    have h := congrFun (colimit.ι_map (TypeFunctorPullback.snd p q) j) x
    have h' : (colim.map (TypeFunctorPullback.snd p q))
        (colimit.ι (TypeFunctorPullback.functor p q) j x) =
        colimit.ι G j ((TypeFunctorPullback.snd p q).app j x) := by
      simpa only [types_comp_apply] using h
    rw [h']
    simpa [isoG, TypeFunctorPullback.snd] using
      congrFun (IsColimit.comp_coconePointUniqueUpToIso_hom
        (colimit.isColimit G) hG j) ((TypeFunctorPullback.snd p q).app j x)

include hF hG hH hp hq in
/-- A compatible pair at the colimit has a representative at one common stage. -/
theorem commonStage (e : Fiber p0 q0) :
    ∃ (j : J) (x : (TypeFunctorPullback.functor p q).obj j),
      cF.ι.app j x.1.1 = e.1.1 ∧ cG.ι.app j x.1.2 = e.1.2 := by
  obtain ⟨j, x, hx⟩ := Types.jointly_surjective_of_isColimit
    (isColimit p q cF cG cH hF hG hH p0 q0 hp hq) e
  exact ⟨j, x, congrArg (fun z : Fiber p0 q0 ↦ z.1.1) hx,
    congrArg (fun z : Fiber p0 q0 ↦ z.1.2) hx⟩

end DaggerModels.OriginalFilteredPullbackColimit
