import IntervalFlagCenter

set_option autoImplicit false

open CategoryTheory MonoidalCategory Opposite Simplicial

universe u

namespace DaggerOriginalIntervalFlagContraction

noncomputable section

open DaggerChosenRigidificationNecklace hiding E
open NecklaceCode DaggerIntervalNecklaceCompletion

variable {a b : (E.{u}).obj (op ⦋0⦌)} {q : SimplexCategoryᵒᵖ}

def rawContraction (p : RawFlag (E.{u}) a b q) (t : (Δ[1] : SSet.{u}).obj q) :
    RawFlag (E.{u}) a b q :=
  ⟨completeObject p.1, squeezeFlag p.1.code.len q
    (NecklaceCode.Flag.map (completionInclusion p.1).hom p.2) t⟩

theorem completion_flag_square {P Q : NecklacesOver (E.{u}) a b}
    (g : NecklacesOver.Hom P Q) (F : NecklaceCode.Flag.{u} P.code q.unop.len) :
    NecklaceCode.Flag.map (completionMap g).hom
      (NecklaceCode.Flag.map (completionInclusion P).hom F) =
      NecklaceCode.Flag.map (completionInclusion Q).hom (NecklaceCode.Flag.map g.hom F) := by
  have h := congrArg NecklacesOver.Hom.hom ((completionInclusions a b).naturality g)
  rw [← NecklaceCode.Flag.map_comp, ← NecklaceCode.Flag.map_comp]
  exact congrArg (fun f ↦ NecklaceCode.Flag.map f F) h.symm

/-- Every original relation generator, not merely a chosen completion arrow. -/
theorem rawContraction_relation {p p' : RawFlag (E.{u}) a b q}
    (h : flagRelation (E.{u}) a b q p p') (t : (Δ[1] : SSet.{u}).obj q) :
    flagRelation (E.{u}) a b q (rawContraction p t) (rawContraction p' t) := by
  obtain ⟨g, hg⟩ := h
  change p'.2 = NecklaceCode.Flag.map g.hom p.2 at hg
  refine ⟨completionMap g, ?_⟩
  change squeezeFlag _ _ (NecklaceCode.Flag.map _ p'.2) t =
    NecklaceCode.Flag.map (completionMap g).hom (squeezeFlag _ _ (NecklaceCode.Flag.map _ p.2) t)
  rw [squeezeFlag_map, completion_flag_square, hg]

theorem rawContraction_operator {r : SimplexCategoryᵒᵖ} (α : q ⟶ r)
    (p : RawFlag (E.{u}) a b q) (t : (Δ[1] : SSet.{u}).obj q) :
    (⟨(rawContraction p t).1,
      NecklaceCode.Flag.restrict α.unop.toOrderHom (rawContraction p t).2⟩ :
        RawFlag (E.{u}) a b r) =
      rawContraction ⟨p.1, NecklaceCode.Flag.restrict α.unop.toOrderHom p.2⟩
        ((Δ[1] : SSet.{u}).map α t) := by
  apply Sigma.ext rfl
  apply heq_of_eq
  rfl

def contractionApp (q : SimplexCategoryᵒᵖ) (x : (flagHom (E.{u}) a b).obj q)
    (t : (Δ[1] : SSet.{u}).obj q) : (flagHom (E.{u}) a b).obj q :=
  Quot.lift (fun p ↦ Quot.mk _ (rawContraction p t))
    (fun _ _ h ↦ Quot.sound (rawContraction_relation h t)) x

theorem contractionApp_mk (p : RawFlag (E.{u}) a b q)
    (t : (Δ[1] : SSet.{u}).obj q) :
    contractionApp q (Quot.mk _ p) t = Quot.mk _ (rawContraction p t) := rfl

def contractionMap : flagHom (E.{u}) a b ⊗ Δ[1] ⟶ flagHom (E.{u}) a b where
  app q x := contractionApp q x.1 x.2
  naturality q r α := by
    funext x
    rcases x with ⟨x, t⟩
    induction x using Quot.ind with | _ p
    exact congrArg (Quot.mk _) (rawContraction_operator α p t).symm

end

end DaggerOriginalIntervalFlagContraction
