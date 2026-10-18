import OriginalFixedObjectPullbacks

/-!
# Pullbacks in the actual original fixed-object strict groupoid category

The original component inverses satisfy the pair constraint, since the full
original functors preserve their degreewise inverses. Thus the actual same-O
pullback retains strictness, with its entire enriched universal property.
-/

set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory DaggerModels
open DaggerOriginalFixedObjectSimplicialCategories DaggerOriginalSimplicialPullbackPairs
open DaggerOriginalFixedObjectPullbacks DaggerOriginalSimplicialDegreeCategory
universe u
namespace DaggerOriginalFixedObjectStrictPullbacks
noncomputable section

/-- The original component inverses again satisfy the full same-degree pullback constraint. -/
theorem pullback_strict {O : Type u} {C D E : FixedStrictGroupoids O}
    (F : C ⟶ E) (G : D ⟶ E) : IsStrictFixed (fixedPullback F.hom G.hom) := by
  intro n x y p
  have hC : @IsIso (degreeObjects (original O C.obj) n)
      (degreeCategory (original O C.obj) n) x y p.1.1 := C.property n x y p.1.1
  have hD : @IsIso (degreeObjects (original O D.obj) n)
      (degreeCategory (original O D.obj) n) x y p.1.2 := D.property n x y p.1.2
  have : @IsIso (degreeObjects (original O E.obj) n)
      (degreeCategory (original O E.obj) n) x y ((F.hom.map x y).app n p.1.1) :=
    E.property n x y ((F.hom.map x y).app n p.1.1)
  have : @IsIso (degreeObjects (original O E.obj) n)
      (degreeCategory (original O E.obj) n) x y ((G.hom.map x y).app n p.1.2) :=
    E.property n x y ((G.hom.map x y).app n p.1.2)
  let a := @inv (degreeObjects (original O C.obj) n)
    (degreeCategory (original O C.obj) n) x y p.1.1 hC
  let b := @inv (degreeObjects (original O D.obj) n)
    (degreeCategory (original O D.obj) n) x y p.1.2 hD
  have hab : (F.hom.map y x).app n a = (G.hom.map y x).app n b := by
    have hF := (degreeFunctor (originalHom F.hom) n).map_inv p.1.1
    have hG := (degreeFunctor (originalHom G.hom) n).map_inv p.1.2
    change (F.hom.map y x).app n a =
      @inv (degreeObjects (original O E.obj) n) (degreeCategory (original O E.obj) n)
        x y ((F.hom.map x y).app n p.1.1) _ at hF
    change (G.hom.map y x).app n b =
      @inv (degreeObjects (original O E.obj) n) (degreeCategory (original O E.obj) n)
        x y ((G.hom.map x y).app n p.1.2) _ at hG
    simp only [hF, hG, p.2]
  let q : (pairedPullback (F.hom.map y x) (G.hom.map y x)).obj n := ⟨(a, b), hab⟩
  refine ⟨⟨q, ?_, ?_⟩⟩
  · apply Subtype.ext
    exact Prod.ext (@IsIso.hom_inv_id (degreeObjects (original O C.obj) n)
        (degreeCategory (original O C.obj) n) x y p.1.1 hC)
      (@IsIso.hom_inv_id (degreeObjects (original O D.obj) n)
        (degreeCategory (original O D.obj) n) x y p.1.2 hD)
  · apply Subtype.ext
    exact Prod.ext (@IsIso.inv_hom_id (degreeObjects (original O C.obj) n)
        (degreeCategory (original O C.obj) n) x y p.1.1 hC)
      (@IsIso.inv_hom_id (degreeObjects (original O D.obj) n)
        (degreeCategory (original O D.obj) n) x y p.1.2 hD)

/-- The original same-O pullback is an actual strict simplicial groupoid. -/
def strictPullback {O : Type u} {C D E : FixedStrictGroupoids O} (F : C ⟶ E) (G : D ⟶ E) :
    FixedStrictGroupoids O := ⟨fixedPullback F.hom G.hom, pullback_strict F G⟩

/-- The full original strict first projection. -/
def strictFst {O : Type u} {C D E : FixedStrictGroupoids O} (F : C ⟶ E) (G : D ⟶ E) :
    strictPullback F G ⟶ C := ObjectProperty.homMk (fixedFst F.hom G.hom)

/-- The full original strict second projection. -/
def strictSnd {O : Type u} {C D E : FixedStrictGroupoids O} (F : C ⟶ E) (G : D ⟶ E) :
    strictPullback F G ⟶ D := ObjectProperty.homMk (fixedSnd F.hom G.hom)

/-- The entire original strict pullback square commutes. -/
theorem strict_comm {O : Type u} {C D E : FixedStrictGroupoids O} (F : C ⟶ E) (G : D ⟶ E) :
    strictFst F G ≫ F = strictSnd F G ≫ G :=
  ObjectProperty.hom_ext _ (fixed_comm F.hom G.hom)

/-- Lift whole original strict functors through the same-O pullback. -/
def strictLift {O : Type u} {A C D E : FixedStrictGroupoids O} {F : C ⟶ E} {G : D ⟶ E}
    (a : A ⟶ C) (b : A ⟶ D) (h : a ≫ F = b ≫ G) : A ⟶ strictPullback F G :=
  ObjectProperty.homMk (fixedLift a.hom b.hom (congrArg (fun k ↦ k.hom) h))

/-- First projection retains the exact whole original strict map. -/
theorem strictLift_fst {O : Type u} {A C D E : FixedStrictGroupoids O} {F : C ⟶ E} {G : D ⟶ E}
    (a : A ⟶ C) (b : A ⟶ D) (h : a ≫ F = b ≫ G) :
    strictLift a b h ≫ strictFst F G = a :=
  ObjectProperty.hom_ext _ (fixedLift_fst a.hom b.hom (congrArg (fun k ↦ k.hom) h))

/-- Second projection retains the exact whole original strict map. -/
theorem strictLift_snd {O : Type u} {A C D E : FixedStrictGroupoids O} {F : C ⟶ E} {G : D ⟶ E}
    (a : A ⟶ C) (b : A ⟶ D) (h : a ≫ F = b ≫ G) :
    strictLift a b h ≫ strictSnd F G = b :=
  ObjectProperty.hom_ext _ (fixedLift_snd a.hom b.hom (congrArg (fun k ↦ k.hom) h))

/-- The full original strict pullback is determined by its full projections. -/
theorem strict_ext {O : Type u} {A C D E : FixedStrictGroupoids O} {F : C ⟶ E} {G : D ⟶ E}
    {a b : A ⟶ strictPullback F G} (h₁ : a ≫ strictFst F G = b ≫ strictFst F G)
    (h₂ : a ≫ strictSnd F G = b ≫ strictSnd F G) : a = b :=
  ObjectProperty.hom_ext _ (fixed_ext (congrArg (fun k ↦ k.hom) h₁)
    (congrArg (fun k ↦ k.hom) h₂))

/-- The actual native limiting-cone witness in the original strict category. -/
def strictIsLimit {O : Type u} {C D E : FixedStrictGroupoids O} (F : C ⟶ E) (G : D ⟶ E) :
    IsLimit (PullbackCone.mk (strictFst F G) (strictSnd F G) (strict_comm F G)) :=
  PullbackCone.IsLimit.mk _ (fun s ↦ strictLift s.fst s.snd s.condition)
    (fun s ↦ strictLift_fst s.fst s.snd s.condition)
    (fun s ↦ strictLift_snd s.fst s.snd s.condition) (by
      intro s m h₁ h₂
      apply strict_ext
      · exact h₁.trans (strictLift_fst s.fst s.snd s.condition).symm
      · exact h₂.trans (strictLift_snd s.fst s.snd s.condition).symm)

/-- Native pullback existence in the unchanged original strict groupoid category. -/
instance strictHasPullback {O : Type u} {C D E : FixedStrictGroupoids O}
    (F : C ⟶ E) (G : D ⟶ E) : HasPullback F G :=
  ⟨⟨⟨PullbackCone.mk (strictFst F G) (strictSnd F G) (strict_comm F G), strictIsLimit F G⟩⟩⟩

/-- Exact four-leg native pullback witness for the original strict square. -/
theorem strictIsPullback {O : Type u} {C D E : FixedStrictGroupoids O}
    (F : C ⟶ E) (G : D ⟶ E) : IsPullback (strictFst F G) (strictSnd F G) F G :=
  IsPullback.of_isLimit (strictIsLimit F G)

end
end DaggerOriginalFixedObjectStrictPullbacks
