import NativeSSetFibrationsOverBaseWeakPullbacks
import SSetRightProper

/-!
# Exact fibre-map weakness in weak squares of actual Kan fibrations

Both total and base maps are the original weak maps, and the same chosen
point object is retained. Relative Brown base change and the retained
SSet right-properness proof show that the actual native fibre map is weak.
This requires the two projections to be fibrations; it is not an assertion
about the original bar projections before replacement.
-/
set_option autoImplicit false
open CategoryTheory Limits HomotopicalAlgebra Simplicial
open DaggerNativeSSetFibrationsOverBaseWeakPullbacks
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerNativeSSetFibrationSquareFibreWeak
noncomputable section

/-- The actual native fibre map for the original commutative total/base square. -/
def fibreMap {X Y B D K : SSet.{u}} (p : X ⟶ B) (q : Y ⟶ D)
    (f : X ⟶ Y) (g : B ⟶ D) (h : p ≫ g = f ≫ q)
    (b : K ⟶ B) (d : K ⟶ D) (hb : b ≫ g = d) : pullback p b ⟶ pullback q d :=
  pullback.lift (pullback.fst p b ≫ f) (pullback.snd p b) (by
    rw [Category.assoc, ← h, pullback.condition_assoc, hb])

/-- The fibre map keeps the original total-map square exactly. -/
theorem fibreMap_fst {X Y B D K : SSet.{u}} (p : X ⟶ B) (q : Y ⟶ D)
    (f : X ⟶ Y) (g : B ⟶ D) (h : p ≫ g = f ≫ q)
    (b : K ⟶ B) (d : K ⟶ D) (hb : b ≫ g = d) :
    fibreMap p q f g h b d hb ≫ pullback.fst q d = pullback.fst p b ≫ f := by
  simp [fibreMap]

/-- The fibre map keeps the unchanged point-object projection exactly. -/
theorem fibreMap_snd {X Y B D K : SSet.{u}} (p : X ⟶ B) (q : Y ⟶ D)
    (f : X ⟶ Y) (g : B ⟶ D) (h : p ≫ g = f ≫ q)
    (b : K ⟶ B) (d : K ⟶ D) (hb : b ≫ g = d) :
    fibreMap p q f g h b d hb ≫ pullback.snd q d = pullback.snd p b := by
  simp [fibreMap]

/-- Weak total/base maps between actual fibrations induce a weak actual fibre map. -/
theorem fibreMap_weakEquivalence {X Y B D K : SSet.{u}} (p : X ⟶ B) (q : Y ⟶ D)
    (f : X ⟶ Y) (g : B ⟶ D) (h : p ≫ g = f ≫ q)
    (b : K ⟶ B) (d : K ⟶ D) (hb : b ≫ g = d)
    [Fibration p] [Fibration q] [WeakEquivalence f] [WeakEquivalence g] :
    WeakEquivalence (fibreMap p q f g h b d hb) := by
  let k := pullback.snd q g
  let t := pullback.fst q g
  let a : X ⟶ pullback q g := pullback.lift f p h.symm
  have ha : a ≫ k = p := by simp [a, k]
  have hat : a ≫ t = f := by simp [a, t]
  have ht : WeakEquivalence t :=
    DaggerSSetRightProper.weakEquivalence_of_isPullback (IsPullback.of_hasPullback q g)
  have := ht
  have : WeakEquivalence a := weakEquivalence_of_postcomp_of_fac hat
  have : Fibration k := inferInstance
  let u := mapOver p k a ha b
  have : WeakEquivalence u := mapOver_weakEquivalence p k a ha b
  have square : IsPullback (pullback.fst k b ≫ t) (pullback.snd k b) q d := by
    simpa only [k, t, hb] using
      (IsPullback.of_hasPullback k b).paste_horiz (IsPullback.of_hasPullback q g)
  let e := square.isoPullback
  have he : u ≫ e.hom = fibreMap p q f g h b d hb := by
    apply pullback.hom_ext
    · rw [Category.assoc, square.isoPullback_hom_fst, ← Category.assoc]
      rw [mapOver_fst, Category.assoc, hat, fibreMap_fst]
    · rw [Category.assoc, square.isoPullback_hom_snd, fibreMap_snd]
      simp [u, mapOver]
  rw [← he]
  infer_instance

end
end DaggerNativeSSetFibrationSquareFibreWeak
