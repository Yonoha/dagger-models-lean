import AmalgamGraph
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs

/-! The arbitrary-target enriched universal property of the two-color quotient. -/

open CategoryTheory Limits MonoidalCategory DaggerModels

universe u

namespace DaggerAmalgamPresentation

noncomputable section

variable (B B' : SimplicialCat.{u, u}) (b : B.Obj) (b' : B'.Obj)
  {E : SimplicialCat.{u, u}}

/-- Both complete factor functors, with only the original object-gluing equation. -/
abbrev Data (E : SimplicialCat.{u, u}) :=
  {F : ∀ c : Bool, factor B B' c ⟶ E // (F false).obj b = (F true).obj b'}

/-- The original Type pushout desc, allowing arbitrary target object maps. -/
def objectDesc (F : Data B B' b b' E) : Objects B B' b b' → E.Obj :=
  Quot.lift (Sum.elim (F.val false).obj (F.val true).obj) (by
    intro _ _ h
    cases h
    exact F.property)

@[simp] theorem objectDesc_label (F : Data B B' b b' E) (c : Bool)
    (x : (factor B B' c).Obj) :
    objectDesc B B' b b' F (label B B' b b' c x) = (F.val c).obj x := by
  cases c <;> rfl

/-- The original factor Hom map, with the actual endpoint equality transports. -/
def rawMap (F : Data B B' b b' E) (c : Bool) (x y : (factor B B' c).Obj) :
    (x ⟶[SSet] y) ⟶ (objectDesc B B' b b' F (label B B' b b' c x) ⟶[SSet]
      objectDesc B B' b b' F (label B B' b b' c y)) :=
  (F.val c).map x y ≫ eqToHom (by rw [objectDesc_label, objectDesc_label])

def endpointEquality (F : Data B B' b b' E) (a z : Objects B B' b b')
    {q : SimplexCategoryᵒᵖ} (e : (graphHom B B' b b' a z).obj q) :
    (objectDesc B B' b b' F (source B B' b b' e.val) ⟶[SSet]
      objectDesc B B' b b' F (target B B' b b' e.val)) =
      (objectDesc B B' b b' F a ⟶[SSet] objectDesc B B' b b' F z) := by
  rw [e.property.1, e.property.2]

def assignedEdges (F : Data B B' b b' E) : graph B B' b b' ⟶ SimplicialCat.underlyingGraph E where
  obj := objectDesc B B' b b' F
  map a z :=
    { app := fun q e ↦
        (rawMap B B' b b' F e.val.1 e.val.2.1 e.val.2.2.1 ≫
          eqToHom (endpointEquality B B' b b' F a z e)).app q e.val.2.2.2
      naturality := by
        intro q q' α
        funext e
        rcases e with ⟨⟨c, x, y, h⟩, he⟩
        exact congrFun ((rawMap B B' b b' F c x y ≫
          eqToHom (endpointEquality B B' b b' F a z ⟨⟨c, x, y, h⟩, he⟩)).naturality α) h }

def freeExtension (F : Data B B' b b' E) : free B B' b b' ⟶ E :=
  SimplicialColimitsFree.lift (assignedEdges B B' b b' F)

theorem freeExtension_factor (F : Data B B' b b' E) (c : Bool)
    (q : SimplexCategoryᵒᵖ) {x y : (factor B B' c).Obj} (h : (x ⟶[SSet] y).obj q) :
    ((freeExtension B B' b b' F).map _ _).app q (factorPath B B' b b' c q h) =
      (rawMap B B' b b' F c x y).app q h := by
  have he := SimplicialColimitsFree.Extension.value_singleton (graph B B' b b')
    (objectDesc B B' b b' F) (assignedEdges B B' b b' F).map q
    ((edgeMap B B' b b' c x y).app q h)
  exact he.trans (by simp [assignedEdges, edgeMap])

theorem freeExtension_kills (F : Data B B' b b' E) :
    SimplicialCat.HomQuotient.Kills (relations B B' b b') (freeExtension B B' b b' F) := by
  intro q a z p p' hp
  cases hp with
  | factorId c x =>
    rw [freeExtension_factor]
    cases c <;>
      exact congrFun (NatTrans.congr_app (F.val _ |>.map_id x) q) PUnit.unit
  | factorComp c h k =>
    rename_i x y z
    change SimplicialColimitsFree.Extension.value (graph B B' b b')
      (objectDesc B B' b b' F) (assignedEdges B B' b b' F).map q
      ((factorPath B B' b b' c q h).comp (factorPath B B' b b' c q k)) = _
    rw [SimplicialColimitsFree.Extension.value_comp]
    change (eComp SSet _ _ _).app q
      (((freeExtension B B' b b' F).map _ _).app q (factorPath B B' b b' c q h),
        ((freeExtension B B' b b' F).map _ _).app q (factorPath B B' b b' c q k)) = _
    rw [freeExtension_factor, freeExtension_factor, freeExtension_factor]
    cases c <;>
      exact (congrFun (NatTrans.congr_app (F.val _ |>.map_comp x y z) q) (h, k)).symm

/-- The full enriched functor descended through the existing contextual quotient. -/
def desc (F : Data B B' b b' E) : Q B B' b b' ⟶ E :=
  SimplicialCat.HomQuotient.descend (relations B B' b b') (freeExtension B B' b b' F)
    (freeExtension_kills B B' b b' F)

theorem leg_desc (F : Data B B' b b' E) (c : Bool) :
    leg B B' b b' c ≫ desc B B' b b' F = F.val c := by
  apply EnrichedFunctor.ext SSet (fun x ↦ objectDesc_label B B' b b' F c x)
  intro x y
  ext q h
  change ((freeExtension B B' b b' F).map _ _ ≫
    eqToHom (by
      change (objectDesc B B' b b' F (label B B' b b' c x) ⟶[SSet]
        objectDesc B B' b b' F (label B B' b b' c y)) = _
      rw [objectDesc_label, objectDesc_label])).app q
      (factorPath B B' b b' c q h) = ((F.val c).map x y).app q h
  rw [SSet.comp_app]
  simp only [types_comp_apply]
  rw [freeExtension_factor]
  cases c <;> rfl

/-- Restrict a functor to both original factor functors. -/
def restrict (H : Q B B' b b' ⟶ E) : Data B B' b b' E :=
  ⟨fun c ↦ leg B B' b b' c ≫ H, congrArg H.obj (glued B B' b b')⟩

theorem freeExtension_restrict (H : Q B B' b b' ⟶ E) :
    freeExtension B B' b b' (restrict B B' b b' H) =
      SimplicialCat.HomQuotient.quotientFunctor (relations B B' b b') ≫ H := by
  apply (SimplicialColimitsFree.homEquiv (graph B B' b b') E).injective
  change SimplicialColimitsFree.restrict
    (SimplicialColimitsFree.lift (assignedEdges B B' b b' (restrict B B' b b' H))) =
      SimplicialColimitsFree.restrict
        (SimplicialCat.HomQuotient.quotientFunctor (relations B B' b b') ≫ H)
  rw [SimplicialColimitsFree.restrict_lift]
  have ho : ∀ a, objectDesc B B' b b' (restrict B B' b b' H) a = H.obj a := by
    intro a
    refine Quot.inductionOn a (fun a ↦ ?_)
    cases a <;> rfl
  apply SimplicialGraph.Map.ext' ho
  intro a z
  ext q e
  rcases e with ⟨⟨c, x, y, h⟩, ha, hz⟩
  subst a
  subst z
  cases c <;>
    simp [assignedEdges, rawMap, restrict, objectDesc, source, target, label, leg, edgeMap,
      SimplicialColimitsFree.restrict] <;> rfl

theorem desc_restrict (H : Q B B' b b' ⟶ E) :
    desc B B' b b' (restrict B B' b b' H) = H := by
  apply SimplicialCat.HomQuotient.quotientFunctor_precomp_injective (relations B B' b b')
  change SimplicialCat.HomQuotient.quotientFunctor (relations B B' b b') ≫
    desc B B' b b' (restrict B B' b b' H) = _
  rw [desc, SimplicialCat.HomQuotient.quotientFunctor_descend, freeExtension_restrict]

/-- Full uniqueness for arbitrary target object maps and both complete factor legs. -/
theorem desc_unique (F : Data B B' b b' E) (H : Q B B' b b' ⟶ E)
    (hH : ∀ c, leg B B' b b' c ≫ H = F.val c) : H = desc B B' b b' F := by
  have hr : restrict B B' b b' H = F := Subtype.ext (funext hH)
  rw [← hr, desc_restrict]

/-- Both inverse laws retain the full enriched functors, not only their vertices. -/
def homEquiv (E : SimplicialCat.{u, u}) : (Q B B' b b' ⟶ E) ≃ Data B B' b b' E where
  toFun := restrict B B' b b'
  invFun := desc B B' b b'
  left_inv := desc_restrict B B' b b'
  right_inv F := Subtype.ext (funext (leg_desc B B' b b' F))

abbrev point : SimplicialCat.{u, u} := SimplicialCat.discrete PUnit.{u + 1}

def leftSelector : point ⟶ B := SimplicialCat.discreteLift PUnit B (fun _ ↦ b)
def rightSelector : point ⟶ B' := SimplicialCat.discreteLift PUnit B' (fun _ ↦ b')

theorem condition : leftSelector B b ≫ leftLeg B B' b b' =
    rightSelector B' b' ≫ rightLeg B B' b b' := by
  apply (SimplicialCat.discreteHomEquiv PUnit (Q B B' b b')).injective
  funext t
  cases t
  exact glued B B' b b'

/-- Any actual compatible square gives the exact input to the quotient desc. -/
def dataOfSquare (F : B ⟶ E) (F' : B' ⟶ E)
    (h : leftSelector B b ≫ F = rightSelector B' b' ≫ F') : Data B B' b b' E :=
  ⟨fun c ↦ match c with | false => F | true => F',
    congrArg (fun t : point ⟶ E ↦ t.obj PUnit.unit) h⟩

def cocone : PushoutCocone (leftSelector B b) (rightSelector B' b') :=
  PushoutCocone.mk (leftLeg B B' b b') (rightLeg B B' b b') (condition B B' b b')

/-- The complete original pushout universal property of the literal quotient. -/
def isColimit : IsColimit (cocone B B' b b') :=
  PushoutCocone.IsColimit.mk _
    (fun s ↦ desc B B' b b' (dataOfSquare B B' b b' s.inl s.inr s.condition))
    (fun s ↦ leg_desc B B' b b' _ false)
    (fun s ↦ leg_desc B B' b b' _ true)
    (fun s m hl hr ↦ desc_unique B B' b b' _ m (by
      intro c
      cases c
      · exact hl
      · exact hr))

theorem isPushout : IsPushout (leftSelector B b) (rightSelector B' b')
    (leftLeg B B' b b') (rightLeg B B' b b') :=
  ⟨⟨condition B B' b b'⟩, ⟨isColimit B B' b b'⟩⟩

end
end DaggerAmalgamPresentation
