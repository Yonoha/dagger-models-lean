import OriginalFixedObjectStrictPullbacks

/-!
# Entire pullbacks of original fixed-object dagger categories and strict groupoids

The original daggers preserve the exact pair constraint because both original
functors preserve dagger. All laws and the whole native limiting cone remain
on the same O. Strictness is the already proved underlying original theorem.
-/

set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory DaggerModels
open DaggerOriginalFixedObjectSimplicialCategories DaggerOriginalFixedObjectDaggerCategories
open DaggerOriginalSimplicialPullbackPairs DaggerOriginalFixedObjectPullbacks
universe u
namespace DaggerOriginalFixedObjectDaggerPullbacks
noncomputable section

/-- The pair of original daggers retains the full exact equality constraint. -/
def homDagger {O : Type u} {C D E : FixedDaggerCategory O}
    (F : C ⟶ E) (G : D ⟶ E) (x y : O) :
    pairedPullback (F.underlying.map x y) (G.underlying.map x y) ⟶
      pairedPullback (F.underlying.map y x) (G.underlying.map y x) where
  app n p := ⟨((C.dagger.dagger x y).app n p.1.1,
    (D.dagger.dagger x y).app n p.1.2), by
      have hF := congrFun (NatTrans.congr_app (F.map_dagger x y) n) p.1.1
      have hG := congrFun (NatTrans.congr_app (G.map_dagger x y) n) p.1.2
      exact hF.symm.trans ((congrArg ((E.dagger.dagger x y).app n) p.2).trans hG)⟩
  naturality _ _ i := by
    funext p
    apply Subtype.ext
    exact Prod.ext (congrFun ((C.dagger.dagger x y).naturality i) p.1.1)
      (congrFun ((D.dagger.dagger x y).naturality i) p.1.2)

/-- The full original dagger structure on the exact same-O pullback enrichment. -/
def pullbackDagger {O : Type u} {C D E : FixedDaggerCategory O}
    (F : C ⟶ E) (G : D ⟶ E) :
    @DaggerSimplicialStructure O (fixedPullback F.underlying G.underlying).enriched := by
  letI := (fixedPullback F.underlying G.underlying).enriched
  refine
    { dagger := homDagger F G
      dagger_involutive := ?_
      dagger_id := ?_
      dagger_comp := ?_ }
  · intro x y
    apply NatTrans.ext
    funext n p
    apply Subtype.ext
    exact Prod.ext (congrFun (NatTrans.congr_app (C.dagger.dagger_involutive x y) n) p.1.1)
      (congrFun (NatTrans.congr_app (D.dagger.dagger_involutive x y) n) p.1.2)
  · intro x
    apply NatTrans.ext
    funext n p
    cases p
    apply Subtype.ext
    exact Prod.ext (congrFun (NatTrans.congr_app (C.dagger.dagger_id x) n) PUnit.unit)
      (congrFun (NatTrans.congr_app (D.dagger.dagger_id x) n) PUnit.unit)
  · intro x y z
    apply NatTrans.ext
    funext n p
    apply Subtype.ext
    exact Prod.ext (congrFun (NatTrans.congr_app (C.dagger.dagger_comp x y z) n)
        (p.1.1.1, p.2.1.1))
      (congrFun (NatTrans.congr_app (D.dagger.dagger_comp x y z) n) (p.1.1.2, p.2.1.2))

/-- The whole original dagger pullback, with exactly the same objects O. -/
def daggerPullback {O : Type u} {C D E : FixedDaggerCategory O}
    (F : C ⟶ E) (G : D ⟶ E) : FixedDaggerCategory O :=
  ⟨fixedPullback F.underlying G.underlying, pullbackDagger F G⟩

/-- The full original first projection preserves dagger. -/
def daggerFst {O : Type u} {C D E : FixedDaggerCategory O}
    (F : C ⟶ E) (G : D ⟶ E) : daggerPullback F G ⟶ C where
  underlying := fixedFst F.underlying G.underlying
  map_dagger _ _ := by apply NatTrans.ext; funext n p; rfl

/-- The full original second projection preserves dagger. -/
def daggerSnd {O : Type u} {C D E : FixedDaggerCategory O}
    (F : C ⟶ E) (G : D ⟶ E) : daggerPullback F G ⟶ D where
  underlying := fixedSnd F.underlying G.underlying
  map_dagger _ _ := by apply NatTrans.ext; funext n p; rfl

/-- The square commutes as entire original dagger functors. -/
theorem dagger_comm {O : Type u} {C D E : FixedDaggerCategory O}
    (F : C ⟶ E) (G : D ⟶ E) : daggerFst F G ≫ F = daggerSnd F G ≫ G :=
  fixedDaggerHom_ext (fixed_comm F.underlying G.underlying)

/-- The whole original lift also preserves the original daggers. -/
def daggerLift {O : Type u} {A C D E : FixedDaggerCategory O} {F : C ⟶ E} {G : D ⟶ E}
    (a : A ⟶ C) (b : A ⟶ D) (h : a ≫ F = b ≫ G) : A ⟶ daggerPullback F G where
  underlying := fixedLift a.underlying b.underlying (congrArg (fun k ↦ k.underlying) h)
  map_dagger x y := by
    apply NatTrans.ext
    funext n p
    apply Subtype.ext
    exact Prod.ext (congrFun (NatTrans.congr_app (a.map_dagger x y) n) p)
      (congrFun (NatTrans.congr_app (b.map_dagger x y) n) p)

/-- The full first original dagger map is recovered exactly. -/
theorem daggerLift_fst {O : Type u} {A C D E : FixedDaggerCategory O} {F : C ⟶ E} {G : D ⟶ E}
    (a : A ⟶ C) (b : A ⟶ D) (h : a ≫ F = b ≫ G) :
    daggerLift a b h ≫ daggerFst F G = a :=
  fixedDaggerHom_ext (fixedLift_fst a.underlying b.underlying
    (congrArg (fun k ↦ k.underlying) h))

/-- The full second original dagger map is recovered exactly. -/
theorem daggerLift_snd {O : Type u} {A C D E : FixedDaggerCategory O} {F : C ⟶ E} {G : D ⟶ E}
    (a : A ⟶ C) (b : A ⟶ D) (h : a ≫ F = b ≫ G) :
    daggerLift a b h ≫ daggerSnd F G = b :=
  fixedDaggerHom_ext (fixedLift_snd a.underlying b.underlying
    (congrArg (fun k ↦ k.underlying) h))

/-- Both full projections determine the entire original dagger map into the pullback. -/
theorem dagger_ext {O : Type u} {A C D E : FixedDaggerCategory O} {F : C ⟶ E} {G : D ⟶ E}
    {a b : A ⟶ daggerPullback F G} (h₁ : a ≫ daggerFst F G = b ≫ daggerFst F G)
    (h₂ : a ≫ daggerSnd F G = b ≫ daggerSnd F G) : a = b :=
  fixedDaggerHom_ext (fixed_ext (congrArg (fun k ↦ k.underlying) h₁)
    (congrArg (fun k ↦ k.underlying) h₂))

/-- Restrict the unchanged whole dagger pullback to the original strict groupoids. -/
def strictDaggerPullback {O : Type u} {C D E : FixedStrictDaggerGroupoids O}
    (F : C ⟶ E) (G : D ⟶ E) : FixedStrictDaggerGroupoids O :=
  ⟨daggerPullback F.hom G.hom,
    DaggerOriginalFixedObjectStrictPullbacks.pullback_strict
      (C := ⟨C.obj.underlying, C.property⟩) (D := ⟨D.obj.underlying, D.property⟩)
      (E := ⟨E.obj.underlying, E.property⟩)
      (ObjectProperty.homMk F.hom.underlying) (ObjectProperty.homMk G.hom.underlying)⟩

/-- Full first strict dagger projection. -/
def strictDaggerFst {O : Type u} {C D E : FixedStrictDaggerGroupoids O}
    (F : C ⟶ E) (G : D ⟶ E) : strictDaggerPullback F G ⟶ C :=
  ObjectProperty.homMk (daggerFst F.hom G.hom)

/-- Full second strict dagger projection. -/
def strictDaggerSnd {O : Type u} {C D E : FixedStrictDaggerGroupoids O}
    (F : C ⟶ E) (G : D ⟶ E) : strictDaggerPullback F G ⟶ D :=
  ObjectProperty.homMk (daggerSnd F.hom G.hom)

/-- The entire original strict dagger square commutes. -/
theorem strictDagger_comm {O : Type u} {C D E : FixedStrictDaggerGroupoids O}
    (F : C ⟶ E) (G : D ⟶ E) : strictDaggerFst F G ≫ F = strictDaggerSnd F G ≫ G :=
  ObjectProperty.hom_ext _ (dagger_comm F.hom G.hom)

/-- Lift whole original strict dagger functors through the same-O pullback. -/
def strictDaggerLift {O : Type u} {A C D E : FixedStrictDaggerGroupoids O}
    {F : C ⟶ E} {G : D ⟶ E} (a : A ⟶ C) (b : A ⟶ D) (h : a ≫ F = b ≫ G) :
    A ⟶ strictDaggerPullback F G :=
  ObjectProperty.homMk (daggerLift a.hom b.hom (congrArg (fun k ↦ k.hom) h))

/-- First projection retains the full original strict dagger map. -/
theorem strictDaggerLift_fst {O : Type u} {A C D E : FixedStrictDaggerGroupoids O}
    {F : C ⟶ E} {G : D ⟶ E} (a : A ⟶ C) (b : A ⟶ D) (h : a ≫ F = b ≫ G) :
    strictDaggerLift a b h ≫ strictDaggerFst F G = a :=
  ObjectProperty.hom_ext _ (daggerLift_fst a.hom b.hom (congrArg (fun k ↦ k.hom) h))

/-- Second projection retains the full original strict dagger map. -/
theorem strictDaggerLift_snd {O : Type u} {A C D E : FixedStrictDaggerGroupoids O}
    {F : C ⟶ E} {G : D ⟶ E} (a : A ⟶ C) (b : A ⟶ D) (h : a ≫ F = b ≫ G) :
    strictDaggerLift a b h ≫ strictDaggerSnd F G = b :=
  ObjectProperty.hom_ext _ (daggerLift_snd a.hom b.hom (congrArg (fun k ↦ k.hom) h))

/-- Both projections determine the full original strict dagger lift. -/
theorem strictDagger_ext {O : Type u} {A C D E : FixedStrictDaggerGroupoids O}
    {F : C ⟶ E} {G : D ⟶ E} {a b : A ⟶ strictDaggerPullback F G}
    (h₁ : a ≫ strictDaggerFst F G = b ≫ strictDaggerFst F G)
    (h₂ : a ≫ strictDaggerSnd F G = b ≫ strictDaggerSnd F G) : a = b :=
  ObjectProperty.hom_ext _ (dagger_ext (congrArg (fun k ↦ k.hom) h₁)
    (congrArg (fun k ↦ k.hom) h₂))

/-- Full native limiting-cone witness in the unchanged original strict dagger category. -/
def strictDaggerIsLimit {O : Type u} {C D E : FixedStrictDaggerGroupoids O}
    (F : C ⟶ E) (G : D ⟶ E) :
    IsLimit (PullbackCone.mk (strictDaggerFst F G) (strictDaggerSnd F G) (strictDagger_comm F G)) :=
  PullbackCone.IsLimit.mk _ (fun s ↦ strictDaggerLift s.fst s.snd s.condition)
    (fun s ↦ strictDaggerLift_fst s.fst s.snd s.condition)
    (fun s ↦ strictDaggerLift_snd s.fst s.snd s.condition) (by
      intro s m h₁ h₂
      apply strictDagger_ext
      · exact h₁.trans (strictDaggerLift_fst s.fst s.snd s.condition).symm
      · exact h₂.trans (strictDaggerLift_snd s.fst s.snd s.condition).symm)

/-- Native pullback existence in the actual original strict dagger groupoid category. -/
instance strictDaggerHasPullback {O : Type u} {C D E : FixedStrictDaggerGroupoids O}
    (F : C ⟶ E) (G : D ⟶ E) : HasPullback F G :=
  ⟨⟨⟨PullbackCone.mk (strictDaggerFst F G) (strictDaggerSnd F G) (strictDagger_comm F G),
    strictDaggerIsLimit F G⟩⟩⟩

/-- The whole native pullback square retains all four original strict dagger legs. -/
theorem strictDaggerIsPullback {O : Type u} {C D E : FixedStrictDaggerGroupoids O}
    (F : C ⟶ E) (G : D ⟶ E) :
    IsPullback (strictDaggerFst F G) (strictDaggerSnd F G) F G :=
  IsPullback.of_isLimit (strictDaggerIsLimit F G)

end
end DaggerOriginalFixedObjectDaggerPullbacks
