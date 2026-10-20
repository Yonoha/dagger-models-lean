import DaggerModels.SimplicialColimitsFree
import DaggerModels.SimplicialHomQuotient
import DaggerModels.DaggerDiscreteObjects
import Mathlib.CategoryTheory.Limits.Types.Pushouts

/-! The literal two-color graph and factor identity/composition relations.
The object type is the original pushout over the identity-only point. -/

open CategoryTheory Limits MonoidalCategory DaggerModels

universe u

namespace DaggerAmalgamPresentation

noncomputable section

variable (B B' : SimplicialCat.{u, u}) (b : B.Obj) (b' : B'.Obj)

def selectLeft : PUnit.{u + 1} ⟶ B.Obj := fun _ ↦ b
def selectRight : PUnit.{u + 1} ⟶ B'.Obj := fun _ ↦ b'

/-- The actual Type pushout, with both original object labels. -/
abbrev Objects := Types.Pushout (selectLeft B b) (selectRight B' b')

def leftObj : B.Obj → Objects B B' b b' :=
  Types.Pushout.inl (selectLeft B b) (selectRight B' b')
def rightObj : B'.Obj → Objects B B' b b' :=
  Types.Pushout.inr (selectLeft B b) (selectRight B' b')

theorem glued : leftObj B B' b b' b = rightObj B B' b b' b' :=
  congrFun (Types.Pushout.condition (selectLeft B b) (selectRight B' b')) PUnit.unit

abbrev factor (c : Bool) : SimplicialCat.{u, u} := if c then B' else B

def label (c : Bool) : (factor B B' c).Obj → Objects B B' b b' :=
  match c with
  | false => leftObj B B' b b'
  | true => rightObj B B' b b'

/-- Each edge retains its color, both original endpoints, and original simplex. -/
abbrev Edge (q : SimplexCategoryᵒᵖ) :=
  Σ c : Bool, Σ x : (factor B B' c).Obj, Σ y : (factor B B' c).Obj,
    (x ⟶[SSet] y).obj q

def source {q : SimplexCategoryᵒᵖ} (e : Edge B B' q) := label B B' b b' e.1 e.2.1
def target {q : SimplexCategoryᵒᵖ} (e : Edge B B' q) := label B B' b b' e.1 e.2.2.1

def graphHom (a z : Objects B B' b b') : SSet.{u} where
  obj q := {e : Edge B B' q // source B B' b b' e = a ∧ target B B' b b' e = z}
  map α e :=
    ⟨⟨e.val.1, e.val.2.1, e.val.2.2.1,
      (e.val.2.1 ⟶[SSet] e.val.2.2.1).map α e.val.2.2.2⟩, e.property⟩
  map_id q := by
    funext e
    apply Subtype.ext
    rcases e with ⟨⟨c, x, y, h⟩, he⟩
    change (⟨c, x, y, (x ⟶[SSet] y).map (𝟙 q) h⟩ : Edge B B' q) = ⟨c, x, y, h⟩
    rw [FunctorToTypes.map_id_apply]
  map_comp α β := by
    funext e
    apply Subtype.ext
    rcases e with ⟨⟨c, x, y, h⟩, he⟩
    change (⟨c, x, y, (x ⟶[SSet] y).map (α ≫ β) h⟩ : Edge B B' _) =
      ⟨c, x, y, (x ⟶[SSet] y).map β ((x ⟶[SSet] y).map α h)⟩
    rw [FunctorToTypes.map_comp_apply]

def graph : SimplicialGraph.{u} := ⟨Objects B B' b b', graphHom B B' b b'⟩
abbrev free := SimplicialColimitsFree.Paths.simplicialCat (graph B B' b b')
abbrev Path (q : SimplexCategoryᵒᵖ) (a z : Objects B B' b b') :=
  SimplicialColimitsFree.Paths.Path (graph B B' b b') q a z

def edgeMap (c : Bool) (x y : (factor B B' c).Obj) :
    (x ⟶[SSet] y) ⟶ graphHom B B' b b' (label B B' b b' c x) (label B B' b b' c y) where
  app q h := ⟨⟨c, x, y, h⟩, rfl, rfl⟩

def factorPath (c : Bool) (q : SimplexCategoryᵒᵖ) {x y : (factor B B' c).Obj}
    (h : (x ⟶[SSet] y).obj q) :
    Path B B' b b' q (label B B' b b' c x) (label B B' b b' c y) :=
  (SimplicialColimitsFree.Paths.inclusion (graph B B' b b') _ _).app q
    ((edgeMap B B' b b' c x y).app q h)

@[simp] theorem map_factorPath (c : Bool) {q q' : SimplexCategoryᵒᵖ} (α : q ⟶ q')
    {x y : (factor B B' c).Obj} (h : (x ⟶[SSet] y).obj q) :
    SimplicialColimitsFree.Paths.map (graph B B' b b') α (factorPath B B' b b' c q h) =
      factorPath B B' b b' c q' ((x ⟶[SSet] y).map α h) := rfl

/-- Only factor identities and compositions; no semantic collapse relation is used. -/
inductive Rel (q : SimplexCategoryᵒᵖ) :
    (a z : Objects B B' b b') → Path B B' b b' q a z → Path B B' b b' q a z → Prop
  | factorId (c : Bool) (x : (factor B B' c).Obj) :
      Rel q _ _ (factorPath B B' b b' c q ((eId SSet x).app q PUnit.unit)) .nil
  | factorComp (c : Bool) {x y z : (factor B B' c).Obj}
      (h : (x ⟶[SSet] y).obj q) (k : (y ⟶[SSet] z).obj q) :
      Rel q _ _ ((factorPath B B' b b' c q h).comp (factorPath B B' b b' c q k))
        (factorPath B B' b b' c q ((eComp SSet x y z).app q (h, k)))

theorem relations_map {q q' : SimplexCategoryᵒᵖ} (α : q ⟶ q')
    {a z : Objects B B' b b'} {p p' : Path B B' b b' q a z}
    (h : Rel B B' b b' q a z p p') :
    Rel B B' b b' q' a z (SimplicialColimitsFree.Paths.map _ α p)
      (SimplicialColimitsFree.Paths.map _ α p') := by
  cases h with
  | factorId c x =>
    rw [map_factorPath]
    have hi := (congrFun ((eId SSet x).naturality α) PUnit.unit).symm
    change (x ⟶[SSet] x).map α ((eId SSet x).app q PUnit.unit) =
      (eId SSet x).app q' PUnit.unit at hi
    rw [hi]
    exact Rel.factorId c x
  | factorComp c h k =>
    rename_i x0 y0 z0
    rw [SimplicialColimitsFree.Paths.map_pathComp, map_factorPath,
      map_factorPath, map_factorPath]
    have hc := congrFun ((eComp SSet x0 y0 z0).naturality α) (h, k)
    change (eComp SSet x0 y0 z0).app q'
      ((x0 ⟶[SSet] y0).map α h, (y0 ⟶[SSet] z0).map α k) =
        (x0 ⟶[SSet] z0).map α ((eComp SSet x0 y0 z0).app q (h, k)) at hc
    rw [← hc]
    exact Rel.factorComp c _ _

def relations : SimplicialCat.HomQuotient.StableHomRel (free B B' b b') where
  rel := Rel B B' b b'
  map_rel := relations_map B B' b b'

/-- The existing enriched quotient retains the literal tagged object pushout. -/
abbrev Q := SimplicialCat.HomQuotient.quotientCategory (relations B B' b b')

def leg (c : Bool) : factor B B' c ⟶ Q B B' b b' where
  obj := label B B' b b' c
  map x y := edgeMap B B' b b' c x y ≫
    SimplicialColimitsFree.Paths.inclusion (graph B B' b b') _ _ ≫
      (SimplicialCat.HomQuotient.quotientFunctor (relations B B' b b')).map _ _
  map_id x := by
    ext q z
    cases z
    exact SimplicialCat.HomQuotient.sound _ q (Rel.factorId c x)
  map_comp x y z := by
    ext q p
    exact (SimplicialCat.HomQuotient.sound _ q (Rel.factorComp c p.1 p.2)).symm

abbrev leftLeg : B ⟶ Q B B' b b' := leg B B' b b' false
abbrev rightLeg : B' ⟶ Q B B' b b' := leg B B' b b' true

end
end DaggerAmalgamPresentation
