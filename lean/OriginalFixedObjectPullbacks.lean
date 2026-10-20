import OriginalSimplicialPullbackPairs

/-!
# Pullbacks of the original fixed-object simplicial categories

The object set remains exactly O. Every Hom is the full simplicial pair fiber
of the original maps, with the original pointwise identities and composition.
-/

set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory DaggerModels
open DaggerOriginalFixedObjectSimplicialCategories DaggerOriginalSimplicialPullbackPairs
universe u
namespace DaggerOriginalFixedObjectPullbacks
noncomputable section

/-- The full original identities belong to the exact pair constraint in every degree. -/
def pullbackId {O : Type u} {C D E : FixedSimplicialCategory O}
    (F : C ⟶ E) (G : D ⟶ E) (x : O) :
    𝟙_ SSet.{u} ⟶ pairedPullback (F.map x x) (G.map x x) where
  app n _ := ⟨((C.enriched.id x).app n PUnit.unit,
    (D.enriched.id x).app n PUnit.unit), by
      exact (congrFun (NatTrans.congr_app (F.map_id x) n) PUnit.unit).trans
        (congrFun (NatTrans.congr_app (G.map_id x) n) PUnit.unit).symm⟩
  naturality _ _ i := by
    funext p
    apply Subtype.ext
    exact Prod.ext (congrFun ((C.enriched.id x).naturality i) PUnit.unit)
      (congrFun ((D.enriched.id x).naturality i) PUnit.unit)

/-- The original two compositions preserve the equality constraint in every degree. -/
def pullbackComp {O : Type u} {C D E : FixedSimplicialCategory O}
    (F : C ⟶ E) (G : D ⟶ E) (x y z : O) :
    pairedPullback (F.map x y) (G.map x y) ⊗ pairedPullback (F.map y z) (G.map y z) ⟶
      pairedPullback (F.map x z) (G.map x z) where
  app n p := ⟨((C.enriched.comp x y z).app n (p.1.1.1, p.2.1.1),
    (D.enriched.comp x y z).app n (p.1.1.2, p.2.1.2)), by
      have hF := congrFun (NatTrans.congr_app (F.map_comp x y z) n) (p.1.1.1, p.2.1.1)
      have hG := congrFun (NatTrans.congr_app (G.map_comp x y z) n) (p.1.1.2, p.2.1.2)
      exact hF.trans ((congrArg (fun a ↦ (E.enriched.comp x y z).app n a)
        (Prod.ext p.1.2 p.2.2)).trans hG.symm)⟩
  naturality _ _ i := by
    funext p
    apply Subtype.ext
    exact Prod.ext (congrFun ((C.enriched.comp x y z).naturality i) (p.1.1.1, p.2.1.1))
      (congrFun ((D.enriched.comp x y z).naturality i) (p.1.1.2, p.2.1.2))

/-- The complete original enrichment on the unchanged O and the exact Hom pullbacks. -/
def fixedPullback {O : Type u} {C D E : FixedSimplicialCategory O}
    (F : C ⟶ E) (G : D ⟶ E) : FixedSimplicialCategory O where
  enriched :=
    { Hom x y := pairedPullback (F.map x y) (G.map x y)
      id := pullbackId F G
      comp := pullbackComp F G
      id_comp x y := by
        apply NatTrans.ext
        funext n p
        apply Subtype.ext
        exact Prod.ext (congrFun (NatTrans.congr_app (C.enriched.id_comp x y) n) p.1.1)
          (congrFun (NatTrans.congr_app (D.enriched.id_comp x y) n) p.1.2)
      comp_id x y := by
        apply NatTrans.ext
        funext n p
        apply Subtype.ext
        exact Prod.ext (congrFun (NatTrans.congr_app (C.enriched.comp_id x y) n) p.1.1)
          (congrFun (NatTrans.congr_app (D.enriched.comp_id x y) n) p.1.2)
      assoc w x y z := by
        apply NatTrans.ext
        funext n p
        apply Subtype.ext
        exact Prod.ext (congrFun (NatTrans.congr_app (C.enriched.assoc w x y z) n)
            (p.1.1.1, (p.2.1.1.1, p.2.2.1.1)))
          (congrFun (NatTrans.congr_app (D.enriched.assoc w x y z) n)
            (p.1.1.2, (p.2.1.1.2, p.2.2.1.2))) }

/-- The entire original first projection preserves the original enrichment. -/
def fixedFst {O : Type u} {C D E : FixedSimplicialCategory O}
    (F : C ⟶ E) (G : D ⟶ E) : fixedPullback F G ⟶ C where
  map x y := pairedFst (F.map x y) (G.map x y)
  map_id _ := by apply NatTrans.ext; funext n p; rfl
  map_comp _ _ _ := by apply NatTrans.ext; funext n p; rfl

/-- The entire original second projection preserves the original enrichment. -/
def fixedSnd {O : Type u} {C D E : FixedSimplicialCategory O}
    (F : C ⟶ E) (G : D ⟶ E) : fixedPullback F G ⟶ D where
  map x y := pairedSnd (F.map x y) (G.map x y)
  map_id _ := by apply NatTrans.ext; funext n p; rfl
  map_comp _ _ _ := by apply NatTrans.ext; funext n p; rfl

/-- The square commutes as whole original enriched functors. -/
theorem fixed_comm {O : Type u} {C D E : FixedSimplicialCategory O}
    (F : C ⟶ E) (G : D ⟶ E) : fixedFst F G ≫ F = fixedSnd F G ≫ G := by
  apply fixedHom_ext
  intro x y
  exact paired_comm (F.map x y) (G.map x y)

/-- Lift two full original functors satisfying the full square equation. -/
def fixedLift {O : Type u} {A C D E : FixedSimplicialCategory O}
    {F : C ⟶ E} {G : D ⟶ E} (a : A ⟶ C) (b : A ⟶ D) (h : a ≫ F = b ≫ G) :
    A ⟶ fixedPullback F G where
  map x y := pairedLift (a.map x y) (b.map x y) (congrArg (fun k ↦ k.map x y) h)
  map_id x := by
    apply NatTrans.ext
    funext n p
    cases p
    apply Subtype.ext
    exact Prod.ext (congrFun (NatTrans.congr_app (a.map_id x) n) PUnit.unit)
      (congrFun (NatTrans.congr_app (b.map_id x) n) PUnit.unit)
  map_comp x y z := by
    apply NatTrans.ext
    funext n p
    apply Subtype.ext
    exact Prod.ext (congrFun (NatTrans.congr_app (a.map_comp x y z) n) p)
      (congrFun (NatTrans.congr_app (b.map_comp x y z) n) p)

/-- First projection recovers the whole first original functor. -/
theorem fixedLift_fst {O : Type u} {A C D E : FixedSimplicialCategory O}
    {F : C ⟶ E} {G : D ⟶ E} (a : A ⟶ C) (b : A ⟶ D) (h : a ≫ F = b ≫ G) :
    fixedLift a b h ≫ fixedFst F G = a := by
  apply fixedHom_ext
  intro x y
  rfl

/-- Second projection recovers the whole second original functor. -/
theorem fixedLift_snd {O : Type u} {A C D E : FixedSimplicialCategory O}
    {F : C ⟶ E} {G : D ⟶ E} (a : A ⟶ C) (b : A ⟶ D) (h : a ≫ F = b ≫ G) :
    fixedLift a b h ≫ fixedSnd F G = b := by
  apply fixedHom_ext
  intro x y
  rfl

/-- Both full projections determine the entire original functor into the pullback. -/
theorem fixed_ext {O : Type u} {A C D E : FixedSimplicialCategory O}
    {F : C ⟶ E} {G : D ⟶ E} {a b : A ⟶ fixedPullback F G}
    (h₁ : a ≫ fixedFst F G = b ≫ fixedFst F G)
    (h₂ : a ≫ fixedSnd F G = b ≫ fixedSnd F G) : a = b := by
  apply fixedHom_ext
  intro x y
  exact paired_ext (congrArg (fun k ↦ k.map x y) h₁) (congrArg (fun k ↦ k.map x y) h₂)

/-- The entire native limiting-cone witness for the original same-O pullback. -/
def fixedIsLimit {O : Type u} {C D E : FixedSimplicialCategory O}
    (F : C ⟶ E) (G : D ⟶ E) :
    IsLimit (PullbackCone.mk (fixedFst F G) (fixedSnd F G) (fixed_comm F G)) :=
  PullbackCone.IsLimit.mk _ (fun s ↦ fixedLift s.fst s.snd s.condition)
    (fun s ↦ fixedLift_fst s.fst s.snd s.condition)
    (fun s ↦ fixedLift_snd s.fst s.snd s.condition) (by
      intro s m h₁ h₂
      apply fixed_ext
      · exact h₁.trans (fixedLift_fst s.fst s.snd s.condition).symm
      · exact h₂.trans (fixedLift_snd s.fst s.snd s.condition).symm)

end
end DaggerOriginalFixedObjectPullbacks
