import OriginalFixedObjectFiniteLimits

/-!
# Full original Hom evaluation of every categorical pullback square

Compare an arbitrary original pullback to the exact pair pullback using its
native limiting cone. Functorial image of that actual isomorphism preserves
all four original Hom maps, so the mapped square is a native SSet pullback.
-/

set_option autoImplicit false
open CategoryTheory Limits DaggerModels
open DaggerOriginalFixedObjectSimplicialCategories DaggerOriginalFixedObjectDaggerCategories
open DaggerOriginalFixedObjectGroupoidClasses DaggerOriginalSimplicialPullbackPairs
open DaggerOriginalFixedObjectStrictPullbacks DaggerOriginalFixedObjectDaggerPullbacks
universe u
namespace DaggerOriginalFixedObjectPullbackEvaluation
noncomputable section

/-- Every whole ordinary strict pullback gives the exact original Hom pullback on all legs. -/
theorem strict_map_isPullback {O : Type u} (x y : O) {P C D E : FixedStrictGroupoids O}
    {p : P ⟶ C} {q : P ⟶ D} {F : C ⟶ E} {G : D ⟶ E} (sq : IsPullback p q F G) :
    IsPullback (p.hom.map x y) (q.hom.map x y) (F.hom.map x y) (G.hom.map x y) := by
  let e := (strictIsLimit F G).conePointUniqueUpToIso sq.isLimit
  have hp : e.hom ≫ p = strictFst F G :=
    (strictIsLimit F G).conePointUniqueUpToIso_hom_comp sq.isLimit (.some .left)
  have hq : e.hom ≫ q = strictSnd F G :=
    (strictIsLimit F G).conePointUniqueUpToIso_hom_comp sq.isLimit (.some .right)
  refine (pairedIsPullback (F.hom.map x y) (G.hom.map x y)).of_iso
    ((strictHomEvaluation O x y).mapIso e) (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · have h := congrArg (fun k ↦ k.hom.map x y) hp
    change e.hom.hom.map x y ≫ p.hom.map x y =
      pairedFst (F.hom.map x y) (G.hom.map x y) at h
    simpa only [Category.comp_id] using h.symm
  · have h := congrArg (fun k ↦ k.hom.map x y) hq
    change e.hom.hom.map x y ≫ q.hom.map x y =
      pairedSnd (F.hom.map x y) (G.hom.map x y) at h
    simpa only [Category.comp_id] using h.symm
  · rfl
  · rfl

/-- Every whole strict dagger pullback retains the exact four original Hom legs. -/
theorem strictDagger_map_isPullback {O : Type u} (x y : O)
    {P C D E : FixedStrictDaggerGroupoids O} {p : P ⟶ C} {q : P ⟶ D}
    {F : C ⟶ E} {G : D ⟶ E} (sq : IsPullback p q F G) :
    IsPullback (p.hom.underlying.map x y) (q.hom.underlying.map x y)
      (F.hom.underlying.map x y) (G.hom.underlying.map x y) := by
  let e := (strictDaggerIsLimit F G).conePointUniqueUpToIso sq.isLimit
  have hp : e.hom ≫ p = strictDaggerFst F G :=
    (strictDaggerIsLimit F G).conePointUniqueUpToIso_hom_comp sq.isLimit (.some .left)
  have hq : e.hom ≫ q = strictDaggerSnd F G :=
    (strictDaggerIsLimit F G).conePointUniqueUpToIso_hom_comp sq.isLimit (.some .right)
  refine (pairedIsPullback (F.hom.underlying.map x y) (G.hom.underlying.map x y)).of_iso
    ((strictDaggerHomEvaluation O x y).mapIso e)
    (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · have h := congrArg (fun k ↦ k.hom.underlying.map x y) hp
    change e.hom.hom.underlying.map x y ≫ p.hom.underlying.map x y =
      pairedFst (F.hom.underlying.map x y) (G.hom.underlying.map x y) at h
    simpa only [Category.comp_id] using h.symm
  · have h := congrArg (fun k ↦ k.hom.underlying.map x y) hq
    change e.hom.hom.underlying.map x y ≫ q.hom.underlying.map x y =
      pairedSnd (F.hom.underlying.map x y) (G.hom.underlying.map x y) at h
    simpa only [Category.comp_id] using h.symm
  · rfl
  · rfl

end
end DaggerOriginalFixedObjectPullbackEvaluation
