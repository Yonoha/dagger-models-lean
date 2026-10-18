import IntervalFlagRaw

set_option autoImplicit false

open CategoryTheory MonoidalCategory Opposite Simplicial

universe u

namespace DaggerOriginalIntervalFlagContraction

noncomputable section

open DaggerChosenRigidificationNecklace hiding E
open NecklaceCode DaggerIntervalNecklaceCompletion

variable (a b : (E.{u}).obj (op ⦋0⦌))

theorem contraction_zero :
    SSet.ι₀ ≫ contractionMap (a := a) (b := b) = SSet.const (center (a := a) (b := b)) := by
  ext q x
  induction x using Quot.ind with | _ p
  change Quot.mk (flagRelation (E.{u}) a b q)
    (rawContraction p (SSet.stdSimplex.const 1 0 q)) = _
  rw [centerAt_const]
  have h := congrFun (NatTrans.congr_app (singleHomotopy_zero.{u} p.1.code.len) q)
    (NecklaceCode.Flag.map (completionInclusion p.1).hom p.2)
  change squeezeFlag p.1.code.len q
    (NecklaceCode.Flag.map (completionInclusion p.1).hom p.2)
    (SSet.stdSimplex.const 1 0 q) = bottomFlag p.1.code.len q.unop.len at h
  change Quot.mk (flagRelation (E.{u}) a b q)
    ⟨completeObject p.1, squeezeFlag p.1.code.len q
      (NecklaceCode.Flag.map (completionInclusion p.1).hom p.2)
      (SSet.stdSimplex.const 1 0 q)⟩ = _
  rw [h]
  exact completed_bottom_center p.1 q

theorem contraction_one :
    SSet.ι₁ ≫ contractionMap (a := a) (b := b) = 𝟙 (flagHom (E.{u}) a b) := by
  ext q x
  induction x using Quot.ind with | _ p
  have h := congrFun (NatTrans.congr_app (singleHomotopy_one.{u} p.1.code.len) q)
    (NecklaceCode.Flag.map (completionInclusion p.1).hom p.2)
  change squeezeFlag p.1.code.len q
    (NecklaceCode.Flag.map (completionInclusion p.1).hom p.2)
    (SSet.stdSimplex.const 1 1 q) =
      NecklaceCode.Flag.map (completionInclusion p.1).hom p.2 at h
  change Quot.mk (flagRelation (E.{u}) a b q)
    ⟨completeObject p.1, squeezeFlag p.1.code.len q
      (NecklaceCode.Flag.map (completionInclusion p.1).hom p.2)
      (SSet.stdSimplex.const 1 1 q)⟩ = Quot.mk _ p
  rw [h]
  exact (Quot.sound ⟨completionInclusion p.1, rfl⟩).symm

def contraction : SSet.Homotopy (SSet.const (center (a := a) (b := b)))
    (𝟙 (flagHom (E.{u}) a b)) where
  h := contractionMap
  h₀ := contraction_zero a b
  h₁ := contraction_one a b

def contractible : SSet.Contractible (flagHom (E.{u}) a b) where
  pt := center
  h := contraction a b

/-- Full all-time quotient formula retaining the supplied original raw flag. -/
theorem contraction_mk (q : SimplexCategoryᵒᵖ) (p : RawFlag (E.{u}) a b q)
    (t : (Δ[1] : SSet.{u}).obj q) :
    (contraction a b).h.app q (Quot.mk _ p, t) = Quot.mk _ (rawContraction p t) := rfl

theorem contraction_operator {q r : SimplexCategoryᵒᵖ} (α : q ⟶ r)
    (x : (flagHom (E.{u}) a b).obj q) (t : (Δ[1] : SSet.{u}).obj q) :
    (flagHom (E.{u}) a b).map α ((contraction a b).h.app q (x, t)) =
      (contraction a b).h.app r
        ((flagHom (E.{u}) a b).map α x, (Δ[1] : SSet.{u}).map α t) :=
  (congrFun ((contraction a b).h.naturality α) (x, t)).symm

end

end DaggerOriginalIntervalFlagContraction
