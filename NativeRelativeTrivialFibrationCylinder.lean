import ActualRigidificationRelativeDirectedHomotopy
import Mathlib.CategoryTheory.LiftingProperties.Basic

/-! Relative cylinder lifts against the native Kan trivial-fibration class.
The boundary data fixes every simplex already fixed by the supplied endomorphism. -/

set_option autoImplicit false
open CategoryTheory Limits Opposite Simplicial MonoidalCategory CartesianMonoidalCategory
open HomotopicalAlgebra
open DaggerOriginalCounitRightConeRelativeHomotopy
open scoped SSet.modelCategoryQuillen
universe u

namespace DaggerNativeRelativeTrivialFibrationCylinder
noncomputable section
attribute [local instance] Classical.propDecidable

def time (q : SimplexCategoryᵒᵖ) (t : Fin 2) : (Δ[1] : SSet.{u}).obj q :=
  SSet.stdSimplex.const 1 t q

theorem time_map {q k : SimplexCategoryᵒᵖ} (α : q ⟶ k) (t : Fin 2) :
    (Δ[1] : SSet.{u}).map α (time q t) = time k t := rfl

theorem time_ne (q : SimplexCategoryᵒᵖ) : time.{u} q 0 ≠ time q 1 := by
  intro h
  have h01 := congrArg
    (fun t : (Δ[1] : SSet.{u}).obj q ↦ (SSet.stdSimplex.objEquiv t).toOrderHom 0) h
  exact (by decide : (0 : Fin 2) ≠ 1) h01

def boundary {X : SSet.{u}} (r : X ⟶ X) : (X ⊗ (Δ[1] : SSet.{u})).Subcomplex where
  obj q := {p | p.2 = time q 0 ∨ p.2 = time q 1 ∨ r.app q p.1 = p.1}
  map {q k} α := by
    intro p hp
    change (Δ[1] : SSet.{u}).map α p.2 = time k 0 ∨
      (Δ[1] : SSet.{u}).map α p.2 = time k 1 ∨
      r.app k (X.map α p.1) = X.map α p.1
    rcases hp with h | h | h
    · exact Or.inl (by rw [h, time_map])
    · exact Or.inr (Or.inl (by rw [h, time_map]))
    · have hn : r.app k (X.map α p.1) = X.map α (r.app q p.1) :=
        congrFun (r.naturality α) p.1
      exact Or.inr (Or.inr (hn.trans (congrArg (X.map α) h)))

def boundaryValue {X : SSet.{u}} (r : X ⟶ X) (q : SimplexCategoryᵒᵖ)
    (p : (boundary r).toSSet.obj q) : X.obj q :=
  if p.val.2 = time q 1 then r.app q p.val.1 else p.val.1

theorem boundaryValue_fixed {X : SSet.{u}} (r : X ⟶ X) (q : SimplexCategoryᵒᵖ)
    (p : (boundary r).toSSet.obj q) (h : r.app q p.val.1 = p.val.1) :
    boundaryValue r q p = p.val.1 := by
  simp only [boundaryValue]
  split_ifs <;> simp_all

theorem boundaryValue_naturality {X : SSet.{u}} (r : X ⟶ X)
    {q k : SimplexCategoryᵒᵖ} (α : q ⟶ k) (p : (boundary r).toSSet.obj q) :
    boundaryValue r k ((boundary r).toSSet.map α p) = X.map α (boundaryValue r q p) := by
  by_cases h1 : p.val.2 = time q 1
  · have hm : (Δ[1] : SSet.{u}).map α p.val.2 = time k 1 := by rw [h1, time_map]
    simp only [boundaryValue, if_pos h1]
    change (if (Δ[1] : SSet.{u}).map α p.val.2 = time k 1
      then r.app k (X.map α p.val.1) else X.map α p.val.1) = _
    rw [if_pos hm]
    exact congrFun (r.naturality α) p.val.1
  · rcases p.property with h0 | h1' | hr
    · have hm : (Δ[1] : SSet.{u}).map α p.val.2 ≠ time k 1 := by
        rw [h0, time_map]
        exact time_ne k
      simp only [boundaryValue, if_neg h1]
      change (if (Δ[1] : SSet.{u}).map α p.val.2 = time k 1
        then r.app k (X.map α p.val.1) else X.map α p.val.1) = _
      exact if_neg hm
    · exact False.elim (h1 h1')
    · have hn : r.app k (X.map α p.val.1) = X.map α (r.app q p.val.1) :=
        congrFun (r.naturality α) p.val.1
      have hm : r.app k (X.map α p.val.1) = X.map α p.val.1 :=
        hn.trans (congrArg (X.map α) hr)
      rw [boundaryValue_fixed r q p hr]
      exact boundaryValue_fixed r k ((boundary r).toSSet.map α p) hm

def boundaryMap {X : SSet.{u}} (r : X ⟶ X) : (boundary r).toSSet ⟶ X where
  app := boundaryValue r
  naturality _ _ α := by
    funext p
    exact boundaryValue_naturality r α p

theorem boundaryMap_over {X Y : SSet.{u}} (f : X ⟶ Y) (r : X ⟶ X)
    (hr : r ≫ f = f) :
    boundaryMap r ≫ f = (boundary r).ι ≫ fst X (Δ[1] : SSet.{u}) ≫ f := by
  ext q p
  change f.app q (boundaryValue r q p) = f.app q p.val.1
  simp only [boundaryValue]
  split_ifs with h
  · exact congrFun (NatTrans.congr_app hr q) p.val.1
  · rfl

def timeInclusion {X : SSet.{u}} (r : X ⟶ X) (t : Fin 2) : X ⟶ (boundary r).toSSet where
  app q x := ⟨(x, time q t), by
    have ht : t = 0 ∨ t = 1 := by omega
    rcases ht with h | h
    · exact Or.inl (congrArg (time q) h)
    · exact Or.inr (Or.inl (congrArg (time q) h))⟩
  naturality _ _ _ := rfl

theorem timeInclusion_ι {X : SSet.{u}} (r : X ⟶ X) (t : Fin 2) :
    timeInclusion r t ≫ (boundary r).ι = timeSlice X t := rfl

theorem timeInclusion_zero {X : SSet.{u}} (r : X ⟶ X) :
    timeInclusion r 0 ≫ boundaryMap r = 𝟙 X := by
  ext q x
  change (if time q 0 = time q 1 then r.app q x else x) = x
  exact if_neg (time_ne q)

theorem timeInclusion_one {X : SSet.{u}} (r : X ⟶ X) :
    timeInclusion r 1 ≫ boundaryMap r = r := by
  ext q x
  change (if time q 1 = time q 1 then r.app q x else x) = r.app q x
  exact if_pos rfl

/-- The native lifting property supplies a whole cylinder relative to the fixed subcomplex. -/
theorem exists_relative_cylinder {X Y : SSet.{u}} (f : X ⟶ Y)
    [Fibration f] [WeakEquivalence f] (r : X ⟶ X) (hr : r ≫ f = f) :
    ∃ H : X ⊗ (Δ[1] : SSet.{u}) ⟶ X,
      (boundary r).ι ≫ H = boundaryMap r ∧ H ≫ f = fst X Δ[1] ≫ f := by
  have : Cofibration (boundary r).ι :=
    (SSet.modelCategoryQuillen.cofibration_iff _).mpr inferInstance
  let sq : CommSq (boundaryMap r) (boundary r).ι f (fst X Δ[1] ≫ f) :=
    ⟨boundaryMap_over f r hr⟩
  exact ⟨sq.lift, sq.fac_left, sq.fac_right⟩

end
end DaggerNativeRelativeTrivialFibrationCylinder
