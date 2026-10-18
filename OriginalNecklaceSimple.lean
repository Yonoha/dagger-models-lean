import ChosenNecklaceIntervalFactor
import ChosenNecklaceCutPushout

set_option autoImplicit false
open CategoryTheory Limits Opposite Simplicial
open DaggerChosenRigidificationNecklace DaggerChosenRigidificationNecklace.NecklaceCode

universe u

namespace DaggerOriginalProductGadget

noncomputable section

/-- Every actual necklace with both endpoints in the source lifts, with both endpoint equations. -/
def NecklaceSimple {A X : SSet.{u}} (j : A ⟶ X) : Prop :=
  ∀ (T : NecklaceCode) (a b : (Δ[0] : SSet.{u}) ⟶ A) (f : T.toSSet ⟶ X),
    pointAt T (ULift.up 0) ≫ f = a ≫ j →
    pointAt T (ULift.up (Fin.last T.len)) ≫ f = b ≫ j →
    ∃ l : T.toSSet ⟶ A, l ≫ j = f ∧
      pointAt T (ULift.up 0) ≫ l = a ∧
      pointAt T (ULift.up (Fin.last T.len)) ≫ l = b

/-- Interval inclusions reuse the original monotone-vertex and interval-factorization theorems. -/
theorem interval_necklaceSimple (T : NecklaceCode) (a b : Fin (T.len + 1))
    (hab : a ≤ b) : NecklaceSimple (intervalι.{u} T a b hab) := by
  intro S x y f hfirst hlast
  have he0 := congrArg SSet.yonedaEquiv hfirst
  have he1 := congrArg SSet.yonedaEquiv hlast
  simp only [SSet.yonedaEquiv_comp, pointAt_vertex] at he0 he1
  have h0 : a ≤ orderMap f 0 := by
    change a ≤ (T.verticesEquiv (f.app _ S.first)).down
    change f.app _ S.first = _ at he0
    rw [he0]
    change a ≤ T.inclusion.app _ ((intervalι T a b hab).app _ (SSet.yonedaEquiv x)) 0
    rw [intervalι_apply]
    exact (intervalEmbedding_bounds T a b hab _).1
  have h1 : orderMap f (Fin.last S.len) ≤ b := by
    change (T.verticesEquiv (f.app _ S.last)).down ≤ b
    change f.app _ S.last = _ at he1
    rw [he1]
    change T.inclusion.app _ ((intervalι T a b hab).app _ (SSet.yonedaEquiv y)) 0 ≤ b
    rw [intervalι_apply]
    exact (intervalEmbedding_bounds T a b hab _).2
  have hf : ∀ z : S.toSSet.obj (op ⦋0⦌),
      a ≤ T.inclusion.app _ (f.app _ z) 0 ∧
        T.inclusion.app _ (f.app _ z) 0 ≤ b := by
    intro z
    let v := (S.verticesEquiv z).down
    have hl := (orderMap f).monotone (Fin.zero_le v)
    have hr := (orderMap f).monotone (Fin.le_last v)
    have he : orderMap f v = T.inclusion.app _ (f.app _ z) 0 := by
      dsimp [v, orderMap, mapVertices]
      rw [S.verticesEquiv.symm_apply_apply]
      rfl
    rw [he] at hl hr
    exact ⟨h0.trans hl, hr.trans h1⟩
  refine ⟨intervalFactor T a b hab f hf, intervalFactor_fac T a b hab f hf, ?_, ?_⟩
  · apply (cancel_mono (intervalι T a b hab)).mp
    rw [Category.assoc, intervalFactor_fac]
    exact hfirst
  · apply (cancel_mono (intervalι T a b hab)).mp
    rw [Category.assoc, intervalFactor_fac]
    exact hlast

theorem cutLeft_necklaceSimple (T : NecklaceCode) (j : Fin (T.len + 1)) :
    NecklaceSimple (cutLeftι.{u} T j) :=
  interval_necklaceSimple T 0 j (Fin.zero_le j)

theorem cutRight_necklaceSimple (T : NecklaceCode) (j : Fin (T.len + 1)) :
    NecklaceSimple (cutRightι.{u} T j) :=
  interval_necklaceSimple T j (Fin.last T.len) (Fin.le_last j)

/-- Taking a product with any simplicial set preserves the full necklace lifting condition. -/
theorem necklaceSimple_prod {A X : SSet.{u}} (j : A ⟶ X)
    (hj : NecklaceSimple j) (K : SSet.{u}) : NecklaceSimple (prod.map (𝟙 K) j) := by
  intro T a b f hfirst hlast
  obtain ⟨l, hl, hl0, hl1⟩ := hj T (a ≫ prod.snd) (b ≫ prod.snd)
    (f ≫ prod.snd)
    (by simpa [Category.assoc] using congrArg (fun t ↦ t ≫ prod.snd) hfirst)
    (by simpa [Category.assoc] using congrArg (fun t ↦ t ≫ prod.snd) hlast)
  refine ⟨prod.lift (f ≫ prod.fst) l, ?_, ?_, ?_⟩
  · apply prod.hom_ext <;> simp [hl]
  · apply prod.hom_ext
    · simpa [Category.assoc] using congrArg (fun t ↦ t ≫ prod.fst) hfirst
    · simpa [Category.assoc] using hl0
  · apply prod.hom_ext
    · simpa [Category.assoc] using congrArg (fun t ↦ t ≫ prod.fst) hlast
    · simpa [Category.assoc] using hl1

end

end DaggerOriginalProductGadget
