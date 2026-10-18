import ChosenFlagHomColimit
import ChosenNecklacesOverWedge
import ChosenNecklaceUnitFlags

open CategoryTheory Limits Opposite Simplicial

universe u

namespace DaggerChosenRigidificationNecklace

noncomputable section

open NecklaceCode

variable {X : SSet.{u}} {a b c d : X.obj (op ⦋0⦌)} {q : SimplexCategoryᵒᵖ}

/-- Original over-X wedge and union of flags, with the full source/target equations. -/
def rawFlagComp (p : RawFlag X a b q) (r : RawFlag X b c q) : RawFlag X a c q :=
  ⟨NecklacesOver.wedge p.1 r.1, NecklaceCode.Flag.wedge p.2 r.2⟩

theorem rawFlagComp_relation_left {p p' : RawFlag X a b q}
    (hp : flagRelation X a b q p p') (r : RawFlag X b c q) :
    flagRelation X a c q (rawFlagComp p r) (rawFlagComp p' r) := by
  obtain ⟨f, hf⟩ := hp
  refine ⟨NecklacesOver.wedgeHom f (NecklacesOver.Hom.id r.1), ?_⟩
  change NecklaceCode.Flag.wedge p'.2 r.2 =
    NecklaceCode.Flag.map (wedgeMap f.hom (NecklaceCode.Hom.id r.1.code))
      (NecklaceCode.Flag.wedge p.2 r.2)
  rw [NecklaceCode.Flag.wedge_map, NecklaceCode.Flag.map_id]
  change p'.2 = NecklaceCode.Flag.map f.hom p.2 at hf
  rw [hf]

theorem rawFlagComp_relation_right (p : RawFlag X a b q) {r r' : RawFlag X b c q}
    (hr : flagRelation X b c q r r') :
    flagRelation X a c q (rawFlagComp p r) (rawFlagComp p r') := by
  obtain ⟨g, hg⟩ := hr
  refine ⟨NecklacesOver.wedgeHom (NecklacesOver.Hom.id p.1) g, ?_⟩
  change NecklaceCode.Flag.wedge p.2 r'.2 =
    NecklaceCode.Flag.map (wedgeMap (NecklaceCode.Hom.id p.1.code) g.hom)
      (NecklaceCode.Flag.wedge p.2 r.2)
  rw [NecklaceCode.Flag.wedge_map, NecklaceCode.Flag.map_id]
  change r'.2 = NecklaceCode.Flag.map g.hom r.2 at hg
  rw [hg]

def flagCompRawLeft (p : RawFlag X a b q) :
    (flagHom X b c).obj q → (flagHom X a c).obj q :=
  Quot.lift (fun r ↦ Quot.mk _ (rawFlagComp p r))
    (fun _ _ h ↦ Quot.sound (rawFlagComp_relation_right p h))

def flagCompApp (x : (flagHom X a b).obj q) (y : (flagHom X b c).obj q) :
    (flagHom X a c).obj q :=
  Quot.lift (fun p ↦ flagCompRawLeft p) (by
    intro p p' hp
    funext y
    induction y using Quot.ind with | _ r
    exact Quot.sound (rawFlagComp_relation_left hp r)) x y

theorem flagCompApp_mk (p : RawFlag X a b q) (r : RawFlag X b c q) :
    flagCompApp (Quot.mk _ p) (Quot.mk _ r) = Quot.mk _ (rawFlagComp p r) := rfl

def flagIdApp (a : X.obj (op ⦋0⦌)) (q : SimplexCategoryᵒᵖ) : (flagHom X a a).obj q :=
  Quot.mk _ ⟨NecklacesOver.point a, NecklaceCode.Flag.pointFlag q.unop.len⟩

theorem flagCompApp_id_left (x : (flagHom X a b).obj q) :
    flagCompApp (flagIdApp a q) x = x := by
  induction x using Quot.ind with | _ p
  exact Quot.sound ⟨NecklacesOver.wedgeLeftUnitOver p.1,
    (NecklaceCode.Flag.wedge_left_unit p.2).symm⟩

theorem flagCompApp_id_right (x : (flagHom X a b).obj q) :
    flagCompApp x (flagIdApp b q) = x := by
  induction x using Quot.ind with | _ p
  exact Quot.sound ⟨NecklacesOver.wedgeRightUnitOver p.1,
    (NecklaceCode.Flag.wedge_right_unit p.2).symm⟩

theorem flagCompApp_assoc (x : (flagHom X a b).obj q) (y : (flagHom X b c).obj q)
    (z : (flagHom X c d).obj q) :
    flagCompApp (flagCompApp x y) z = flagCompApp x (flagCompApp y z) := by
  induction x using Quot.ind with | _ p
  induction y using Quot.ind with | _ r
  induction z using Quot.ind with | _ s
  exact Quot.sound ⟨NecklacesOver.wedgeAssocOver p.1 r.1 s.1,
    (NecklaceCode.Flag.wedge_assoc p.2 r.2 s.2).symm⟩

theorem flagCompApp_operator {k : SimplexCategoryᵒᵖ} (α : q ⟶ k)
    (x : (flagHom X a b).obj q) (y : (flagHom X b c).obj q) :
    (flagHom X a c).map α (flagCompApp x y) =
      flagCompApp ((flagHom X a b).map α x) ((flagHom X b c).map α y) := by
  induction x using Quot.ind with | _ p
  induction y using Quot.ind with | _ r
  apply congrArg (Quot.mk _)
  apply Sigma.ext rfl
  exact heq_of_eq (NecklaceCode.Flag.wedge_restrict _ _ _)

theorem flagIdApp_operator {k : SimplexCategoryᵒᵖ} (α : q ⟶ k)
    (a : X.obj (op ⦋0⦌)) : (flagHom X a a).map α (flagIdApp a q) = flagIdApp a k := by
  apply congrArg (Quot.mk _)
  apply Sigma.ext rfl
  exact heq_of_eq (NecklaceCode.Flag.ext (fun _ ↦ rfl))

end

end DaggerChosenRigidificationNecklace
