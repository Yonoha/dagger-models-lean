import DaggerModels.SimplicialColimitsFree
import DaggerModels.SimplicialHomQuotient
import DaggerModels.OrdinaryTwoObjectCell
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs

/-! The actual ordinary one-cell pushout as the existing enriched path quotient.
The original attaching map need not be a monomorphism. No word normalization,
mapping-space monomorphism or weak equivalence is asserted here. -/

open CategoryTheory Limits MonoidalCategory DaggerModels

universe u

namespace DaggerRelativeOneCellPresentation

noncomputable section

variable (C : SimplicialCat.{u, u}) (x y : C.Obj) {K L : SSet.{u}}

/-- Old arrows and the original L letters with their literal endpoint equalities. -/
def graphHom (a b : C.Obj) : SSet.{u} where
  obj q := (a ⟶[SSet] b).obj q ⊕ {l : L.obj q // a = x ∧ b = y}
  map α := Sum.map ((a ⟶[SSet] b).map α) (fun l ↦ ⟨L.map α l.val, l.property⟩)
  map_id q := by
    funext w
    cases w with
    | inl h => simp
    | inr l => simp
  map_comp α β := by
    funext w
    cases w with
    | inl h => simp
    | inr l => simp

/-- The graph has exactly the original object type. -/
def graph : SimplicialGraph.{u} := ⟨C.Obj, graphHom C x y (L := L)⟩

abbrev free : SimplicialCat.{u, u} :=
  SimplicialColimitsFree.Paths.simplicialCat (graph C x y (L := L))

abbrev Path (q : SimplexCategoryᵒᵖ) (a b : C.Obj) :=
  SimplicialColimitsFree.Paths.Path (graph C x y (L := L)) q a b

def edgePath (q : SimplexCategoryᵒᵖ) {a b : C.Obj}
    (e : (graphHom C x y (L := L) a b).obj q) : Path C x y (L := L) q a b :=
  (SimplicialColimitsFree.Paths.inclusion (graph C x y (L := L)) a b).app q e

def oldPath (q : SimplexCategoryᵒᵖ) {a b : C.Obj} (h : (a ⟶[SSet] b).obj q) :
    Path C x y (L := L) q a b := edgePath C x y q (.inl h)

def newPath (q : SimplexCategoryᵒᵖ) (l : L.obj q) : Path C x y (L := L) q x y :=
  edgePath C x y q (.inr ⟨l, rfl, rfl⟩)

@[simp] theorem map_oldPath {q q' : SimplexCategoryᵒᵖ} (α : q ⟶ q')
    {a b : C.Obj} (h : (a ⟶[SSet] b).obj q) :
    SimplicialColimitsFree.Paths.map (graph C x y (L := L)) α (oldPath C x y q h) =
      oldPath C x y q' ((a ⟶[SSet] b).map α h) := rfl

@[simp] theorem map_newPath {q q' : SimplexCategoryᵒᵖ} (α : q ⟶ q') (l : L.obj q) :
    SimplicialColimitsFree.Paths.map (graph C x y (L := L)) α (newPath C x y q l) =
      newPath C x y q' (L.map α l) := rfl

variable (i : K ⟶ L) (u0 : K ⟶ (x ⟶[SSet] y))

/-- Precisely the original identity, composition, and original K-letter relations. -/
inductive Rel (q : SimplexCategoryᵒᵖ) :
    (a b : C.Obj) → Path C x y (L := L) q a b → Path C x y (L := L) q a b → Prop
  | oldId (a : C.Obj) :
      Rel q a a (oldPath C x y q ((eId SSet a).app q PUnit.unit)) .nil
  | oldComp {a b c : C.Obj} (h : (a ⟶[SSet] b).obj q) (j : (b ⟶[SSet] c).obj q) :
      Rel q a c ((oldPath C x y q h).comp (oldPath C x y q j))
        (oldPath C x y q ((eComp SSet a b c).app q (h, j)))
  | attaching (k : K.obj q) :
      Rel q x y (newPath C x y q (i.app q k)) (oldPath C x y q (u0.app q k))

theorem relations_map {q q' : SimplexCategoryᵒᵖ} (α : q ⟶ q') {a b : C.Obj}
    {p p' : Path C x y (L := L) q a b} (h : Rel C x y i u0 q a b p p') :
    Rel C x y i u0 q' a b (SimplicialColimitsFree.Paths.map _ α p)
      (SimplicialColimitsFree.Paths.map _ α p') := by
  cases h with
  | oldId a =>
    change Rel C x y i u0 q' a a
      (SimplicialColimitsFree.Paths.map _ α (oldPath C x y q ((eId SSet a).app q PUnit.unit))) .nil
    rw [map_oldPath]
    have hi := (congrFun ((eId SSet a).naturality α) PUnit.unit).symm
    change (a ⟶[SSet] a).map α ((eId SSet a).app q PUnit.unit) =
      (eId SSet a).app q' PUnit.unit at hi
    rw [hi]
    exact Rel.oldId _
  | oldComp h j =>
    rename_i middle
    rw [SimplicialColimitsFree.Paths.map_pathComp, map_oldPath, map_oldPath, map_oldPath]
    have hc := congrFun ((eComp SSet a middle b).naturality α) (h, j)
    change (eComp SSet a middle b).app q'
      ((a ⟶[SSet] middle).map α h, (middle ⟶[SSet] b).map α j) =
        (a ⟶[SSet] b).map α ((eComp SSet a middle b).app q (h, j)) at hc
    rw [← hc]
    exact Rel.oldComp _ _
  | attaching k =>
    rw [map_newPath, map_oldPath]
    have hi := (congrFun (i.naturality α) k).symm
    have hu := (congrFun (u0.naturality α) k).symm
    change L.map α (i.app q k) = i.app q' (K.map α k) at hi
    change (x ⟶[SSet] y).map α (u0.app q k) = u0.app q' (K.map α k) at hu
    rw [hi, hu]
    exact Rel.attaching _

def relations : SimplicialCat.HomQuotient.StableHomRel (free C x y (L := L)) where
  rel := Rel C x y i u0
  map_rel := relations_map C x y i u0

/-- The existing enriched hom quotient keeps literally the original objects. -/
abbrev Q : SimplicialCat.{u, u} := SimplicialCat.HomQuotient.quotientCategory (relations C x y i u0)

/-- The original category maps into the quotient by its original old arrows. -/
def v : C ⟶ Q C x y i u0 where
  obj := id
  map a b :=
    { app := fun q h ↦ SimplicialCat.HomQuotient.mk (relations C x y i u0) q (oldPath C x y q h)
      naturality := by intros; rfl }
  map_id a := by
    ext q z
    cases z
    exact SimplicialCat.HomQuotient.sound _ q (Rel.oldId a)
  map_comp a b c := by
    ext q p
    exact (SimplicialCat.HomQuotient.sound _ q (Rel.oldComp p.1 p.2)).symm

/-- The original new L edge, retaining the actual x and y. -/
def newMap : L ⟶ SimplicialCat.HomQuotient.hom (relations C x y i u0) x y where
  app q l := SimplicialCat.HomQuotient.mk (relations C x y i u0) q (newPath C x y q l)
  naturality := by intros; rfl

def t : OrdinaryTwoObjectCell.cell L ⟶ Q C x y i u0 :=
  OrdinaryTwoObjectCell.fromData L _ x y (newMap C x y i u0)

theorem attaching_equation : i ≫ newMap C x y i u0 = u0 ≫ (v C x y i u0).map x y := by
  ext q k
  exact SimplicialCat.HomQuotient.sound _ q (Rel.attaching k)

theorem condition : OrdinaryTwoObjectCell.functor.map i ≫ t C x y i u0 =
    OrdinaryTwoObjectCell.fromData K C x y u0 ≫ v C x y i u0 := by
  unfold t
  rw [← OrdinaryTwoObjectCell.fromData_naturality_left,
    OrdinaryTwoObjectCell.fromData_naturality_right]
  exact congrArg (OrdinaryTwoObjectCell.fromData K (Q C x y i u0) x y)
    (attaching_equation C x y i u0)

variable {E : SimplicialCat.{u, u}}

/-- An arbitrary old functor and a new edge assign every tagged generating arrow. -/
def assignedEdges (F : C ⟶ E) (ell : L ⟶ (F.obj x ⟶[SSet] F.obj y)) (a b : C.Obj) :
    graphHom C x y (L := L) a b ⟶ (F.obj a ⟶[SSet] F.obj b) where
  app q := Sum.elim ((F.map a b).app q) (fun l ↦
    (ell ≫ eqToHom (by rw [← l.property.1, ← l.property.2])).app q l.val)
  naturality {q q'} α := by
    funext w
    cases w with
    | inl h => exact congrFun ((F.map a b).naturality α) h
    | inr l =>
      rcases l with ⟨l, ha, hb⟩
      subst a
      subst b
      simpa [graphHom] using congrFun (ell.naturality α) l

/-- Reuse the complete existing enriched extension of finite paths. -/
def freeExtension (F : C ⟶ E) (ell : L ⟶ (F.obj x ⟶[SSet] F.obj y)) :
    free C x y (L := L) ⟶ E :=
  SimplicialColimitsFree.Extension.extend (graph C x y) F.obj (assignedEdges C x y F ell)

theorem freeExtension_old (F : C ⟶ E) (ell : L ⟶ (F.obj x ⟶[SSet] F.obj y))
    (q : SimplexCategoryᵒᵖ) {a b : C.Obj} (h : (a ⟶[SSet] b).obj q) :
    ((freeExtension C x y F ell).map a b).app q (oldPath C x y q h) =
      (F.map a b).app q h :=
  SimplicialColimitsFree.Extension.value_singleton (graph C x y) F.obj
    (assignedEdges C x y F ell) q (Sum.inl h)

theorem freeExtension_new (F : C ⟶ E) (ell : L ⟶ (F.obj x ⟶[SSet] F.obj y))
    (q : SimplexCategoryᵒᵖ) (l : L.obj q) :
    ((freeExtension C x y F ell).map x y).app q (newPath C x y q l) = ell.app q l := by
  have h := SimplicialColimitsFree.Extension.value_singleton (graph C x y) F.obj
    (assignedEdges C x y F ell) q (Sum.inr ⟨l, rfl, rfl⟩)
  exact h.trans (by simp [assignedEdges])

theorem kill_relation (F : C ⟶ E) (ell : L ⟶ (F.obj x ⟶[SSet] F.obj y))
    (h : i ≫ ell = u0 ≫ F.map x y) (q : SimplexCategoryᵒᵖ) (a b : C.Obj)
    (p p' : Path C x y (L := L) q a b) (hp : Rel C x y i u0 q a b p p') :
    ((freeExtension C x y F ell).map a b).app q p =
      ((freeExtension C x y F ell).map a b).app q p' := by
  cases hp with
  | oldId a =>
    rw [freeExtension_old]
    exact congrFun (NatTrans.congr_app (F.map_id a) q) PUnit.unit
  | oldComp h j =>
    rename_i middle
    change SimplicialColimitsFree.Extension.value (graph C x y) F.obj
      (assignedEdges C x y F ell) q
      ((oldPath C x y q h).comp (oldPath C x y q j)) = _
    rw [SimplicialColimitsFree.Extension.value_comp]
    change (eComp SSet (F.obj a) (F.obj middle) (F.obj b)).app q
      (((freeExtension C x y F ell).map a middle).app q (oldPath C x y q h),
        ((freeExtension C x y F ell).map middle b).app q (oldPath C x y q j)) = _
    rw [freeExtension_old, freeExtension_old, freeExtension_old]
    exact (congrFun (NatTrans.congr_app (F.map_comp a middle b) q) (h, j)).symm
  | attaching k =>
    rw [freeExtension_new, freeExtension_old]
    exact congrFun (NatTrans.congr_app h q) k


theorem freeExtension_kills (F : C ⟶ E) (ell : L ⟶ (F.obj x ⟶[SSet] F.obj y))
    (h : i ≫ ell = u0 ≫ F.map x y) :
    SimplicialCat.HomQuotient.Kills (relations C x y i u0) (freeExtension C x y F ell) :=
  kill_relation C x y i u0 F ell h

/-- The actual arbitrary-object-map functor descended through the existing quotient. -/
def desc (F : C ⟶ E) (ell : L ⟶ (F.obj x ⟶[SSet] F.obj y))
    (h : i ≫ ell = u0 ≫ F.map x y) : Q C x y i u0 ⟶ E :=
  SimplicialCat.HomQuotient.descend (relations C x y i u0) (freeExtension C x y F ell)
    (freeExtension_kills C x y i u0 F ell h)

theorem v_desc (F : C ⟶ E) (ell : L ⟶ (F.obj x ⟶[SSet] F.obj y))
    (h : i ≫ ell = u0 ≫ F.map x y) : v C x y i u0 ≫ desc C x y i u0 F ell h = F := by
  apply EnrichedFunctor.ext SSet
    (F := v C x y i u0 ≫ desc C x y i u0 F ell h) (G := F) (fun _ ↦ rfl)
  intro a b
  simp only [eqToHom_refl, Category.comp_id]
  ext q j
  exact freeExtension_old C x y F ell q j

theorem newMap_desc (F : C ⟶ E) (ell : L ⟶ (F.obj x ⟶[SSet] F.obj y))
    (h : i ≫ ell = u0 ≫ F.map x y) :
    newMap C x y i u0 ≫ (desc C x y i u0 F ell h).map x y = ell := by
  ext q l
  exact freeExtension_new C x y F ell q l

theorem t_desc (F : C ⟶ E) (ell : L ⟶ (F.obj x ⟶[SSet] F.obj y))
    (h : i ≫ ell = u0 ≫ F.map x y) :
    t C x y i u0 ≫ desc C x y i u0 F ell h =
      OrdinaryTwoObjectCell.fromData L E (F.obj x) (F.obj y) ell := by
  unfold t
  rw [OrdinaryTwoObjectCell.fromData_naturality_right, newMap_desc]
  rfl

theorem freeExtension_restrict (H : Q C x y i u0 ⟶ E) :
    freeExtension C x y (v C x y i u0 ≫ H) (newMap C x y i u0 ≫ H.map x y) =
      SimplicialCat.HomQuotient.quotientFunctor (relations C x y i u0) ≫ H := by
  apply (SimplicialColimitsFree.homEquiv (graph C x y) E).injective
  change SimplicialColimitsFree.restrict
    (SimplicialColimitsFree.lift (G := graph C x y) (C := E)
      ⟨H.obj, assignedEdges C x y (v C x y i u0 ≫ H)
      (newMap C x y i u0 ≫ H.map x y)⟩) = _
  rw [SimplicialColimitsFree.restrict_lift]
  apply SimplicialGraph.Map.ext'
    (f := ⟨H.obj, assignedEdges C x y (v C x y i u0 ≫ H)
      (newMap C x y i u0 ≫ H.map x y)⟩)
    (g := SimplicialColimitsFree.restrict
      (SimplicialCat.HomQuotient.quotientFunctor (relations C x y i u0) ≫ H))
    (fun _ ↦ rfl)
  intro a b
  simp only [eqToHom_refl, Category.comp_id]
  ext q w
  cases w with
  | inl h => rfl
  | inr l =>
    rcases l with ⟨l, ha, hb⟩
    subst a
    subst b
    simp only [assignedEdges, eqToHom_refl, Category.comp_id, Sum.elim_inr]
    rfl

/-- The original compatible data, allowing every old functor and arbitrary object images. -/
abbrev Data (E : SimplicialCat.{u, u}) :=
  Σ F : C ⟶ E, {ell : L ⟶ (F.obj x ⟶[SSet] F.obj y) // i ≫ ell = u0 ≫ F.map x y}

theorem data_ext {F G : C ⟶ E}
    {ell : L ⟶ (F.obj x ⟶[SSet] F.obj y)} {ell' : L ⟶ (G.obj x ⟶[SSet] G.obj y)}
    {h : i ≫ ell = u0 ≫ F.map x y} {h' : i ≫ ell' = u0 ≫ G.map x y}
    (hF : F = G) (hEll : HEq ell ell') :
    (⟨F, ell, h⟩ : Data C x y i u0 E) = ⟨G, ell', h'⟩ := by
  cases hF
  cases hEll
  rfl

/-- The full enriched hom equivalence, with the original attaching equation. -/
def homEquiv (E : SimplicialCat.{u, u}) :
    (Q C x y i u0 ⟶ E) ≃ Data C x y i u0 E where
  toFun H := ⟨v C x y i u0 ≫ H, newMap C x y i u0 ≫ H.map x y, by
    change i ≫ (newMap C x y i u0 ≫ H.map x y) =
      u0 ≫ ((v C x y i u0).map x y ≫ H.map x y)
    rw [← Category.assoc, attaching_equation, Category.assoc]⟩
  invFun d := desc C x y i u0 d.1 d.2.val d.2.property
  left_inv H := by
    apply SimplicialCat.HomQuotient.quotientFunctor_precomp_injective (relations C x y i u0)
    dsimp only [desc]
    rw [SimplicialCat.HomQuotient.quotientFunctor_descend]
    exact freeExtension_restrict C x y i u0 H
  right_inv d := by
    rcases d with ⟨F, ell, h⟩
    apply data_ext C x y i u0 (v_desc C x y i u0 F ell h)
    exact heq_of_eq (newMap_desc C x y i u0 F ell h)

/-- Full functor equality gives the component equality with its actual object transport. -/
theorem enriched_congr_map {A B : SimplicialCat.{u, u}} {F G : A ⟶ B}
    (h : F = G) (a b : A.Obj) : F.map a b ≫ eqToHom (by rw [h]) = G.map a b := by
  cases h
  simp

open TwoObjectDaggerGraph (left right)

variable (g : OrdinaryTwoObjectCell.cell L ⟶ E) (F : C ⟶ E)
  (w : OrdinaryTwoObjectCell.functor.map i ≫ g =
    OrdinaryTwoObjectCell.fromData K C x y u0 ≫ F)

include w in
theorem cocone_left : g.obj left = F.obj x :=
  congrArg (fun H : OrdinaryTwoObjectCell.cell K ⟶ E ↦ H.obj left) w

include w in
theorem cocone_right : g.obj right = F.obj y :=
  congrArg (fun H : OrdinaryTwoObjectCell.cell K ⟶ E ↦ H.obj right) w

/-- The original new edge, transported by precisely the two cocone object equalities. -/
def coconeEdge : L ⟶ (F.obj x ⟶[SSet] F.obj y) :=
  g.map left right ≫ eqToHom (by
    rw [cocone_left C x y i u0 g F w, cocone_right C x y i u0 g F w])

theorem coconeEdge_equation : i ≫ coconeEdge C x y i u0 g F w = u0 ≫ F.map x y := by
  have h := enriched_congr_map w left right
  simpa only [Category.assoc] using h

theorem cellData_transport (gx gy fx fy : E.Obj) (hx : gx = fx) (hy : gy = fy)
    (ell : L ⟶ (gx ⟶[SSet] gy)) :
    (⟨fx, fy, ell ≫ eqToHom (by rw [hx, hy])⟩ :
      Σ a : E.Obj, Σ b : E.Obj, (L ⟶ (a ⟶[SSet] b))) = ⟨gx, gy, ell⟩ := by
  cases hx
  cases hy
  simp

theorem fromData_coconeEdge :
    OrdinaryTwoObjectCell.fromData L E (F.obj x) (F.obj y) (coconeEdge C x y i u0 g F w) =
      g := by
  apply (OrdinaryTwoObjectCell.homEquiv L E).injective
  exact cellData_transport _ _ _ _ (cocone_left C x y i u0 g F w)
    (cocone_right C x y i u0 g F w) (g.map left right)

def coconeDesc : Q C x y i u0 ⟶ E :=
  desc C x y i u0 F (coconeEdge C x y i u0 g F w) (coconeEdge_equation C x y i u0 g F w)

theorem v_coconeDesc : v C x y i u0 ≫ coconeDesc C x y i u0 g F w = F :=
  v_desc C x y i u0 F _ _

theorem t_coconeDesc : t C x y i u0 ≫ coconeDesc C x y i u0 g F w = g := by
  unfold coconeDesc
  rw [t_desc, fromData_coconeEdge]

theorem hom_ext {H H' : Q C x y i u0 ⟶ E}
    (hv : v C x y i u0 ≫ H = v C x y i u0 ≫ H')
    (ht : t C x y i u0 ≫ H = t C x y i u0 ≫ H') : H = H' := by
  apply (homEquiv C x y i u0 E).injective
  apply data_ext C x y i u0 hv
  exact congr_arg_heq (fun T : OrdinaryTwoObjectCell.cell L ⟶ E ↦ T.map left right) ht

theorem coconeDesc_unique (H : Q C x y i u0 ⟶ E)
    (ht : t C x y i u0 ≫ H = g) (hv : v C x y i u0 ≫ H = F) :
    H = coconeDesc C x y i u0 g F w :=
  hom_ext C x y i u0 (hv.trans (v_coconeDesc C x y i u0 g F w).symm)
    (ht.trans (t_coconeDesc C x y i u0 g F w).symm)

def cocone : PushoutCocone (OrdinaryTwoObjectCell.functor.map i)
    (OrdinaryTwoObjectCell.fromData K C x y u0) :=
  PushoutCocone.mk (t C x y i u0) (v C x y i u0) (condition C x y i u0)

def isColimit : IsColimit (cocone C x y i u0) :=
  PushoutCocone.IsColimit.mk (condition C x y i u0)
    (fun s ↦ coconeDesc C x y i u0 s.inl s.inr s.condition)
    (fun s ↦ t_coconeDesc C x y i u0 s.inl s.inr s.condition)
    (fun s ↦ v_coconeDesc C x y i u0 s.inl s.inr s.condition)
    (by
      intro s H ht hv
      exact coconeDesc_unique C x y i u0 s.inl s.inr s.condition H ht hv)

/-- The full original ordinary enriched free-cell square is an actual pushout. -/
theorem isPushout : IsPushout (OrdinaryTwoObjectCell.functor.map i)
    (OrdinaryTwoObjectCell.fromData K C x y u0) (t C x y i u0) (v C x y i u0) :=
  IsPushout.of_isColimit (isColimit C x y i u0)

variable {D : SimplicialCat.{u, u}} (g0 : OrdinaryTwoObjectCell.cell L ⟶ D) (f : C ⟶ D)
  (sq : IsPushout (OrdinaryTwoObjectCell.functor.map i)
    (OrdinaryTwoObjectCell.fromData K C x y u0) g0 f)

/-- The canonical full enriched isomorphism to any original pushout apex. -/
def originalIso : Q C x y i u0 ≅ D :=
  (isPushout C x y i u0).isoIsPushout _ _ sq

theorem v_originalIso : v C x y i u0 ≫ (originalIso C x y i u0 g0 f sq).hom = f :=
  IsPushout.inr_isoIsPushout_hom _ _ (isPushout C x y i u0) sq

theorem t_originalIso : t C x y i u0 ≫ (originalIso C x y i u0 g0 f sq).hom = g0 :=
  IsPushout.inl_isoIsPushout_hom _ _ (isPushout C x y i u0) sq

theorem f_originalIso_inv : f ≫ (originalIso C x y i u0 g0 f sq).inv = v C x y i u0 :=
  IsPushout.inr_isoIsPushout_inv _ _ (isPushout C x y i u0) sq

theorem g_originalIso_inv : g0 ≫ (originalIso C x y i u0 g0 f sq).inv = t C x y i u0 :=
  IsPushout.inl_isoIsPushout_inv _ _ (isPushout C x y i u0) sq

theorem originalIso_obj (a : C.Obj) : (originalIso C x y i u0 g0 f sq).hom.obj a = f.obj a :=
  congrArg (fun H : C ⟶ D ↦ H.obj a) (v_originalIso C x y i u0 g0 f sq)

theorem originalIso_map (a b : C.Obj) :
    (v C x y i u0).map a b ≫ (originalIso C x y i u0 g0 f sq).hom.map a b ≫
      eqToHom (by rw [originalIso_obj C x y i u0 g0 f sq a,
        originalIso_obj C x y i u0 g0 f sq b]) = f.map a b :=
  enriched_congr_map (v_originalIso C x y i u0 g0 f sq) a b

theorem originalIso_edge :
    newMap C x y i u0 ≫ (originalIso C x y i u0 g0 f sq).hom.map x y ≫
      eqToHom (by
        have ht := t_originalIso C x y i u0 g0 f sq
        have hx := congrArg (fun H : OrdinaryTwoObjectCell.cell L ⟶ D ↦ H.obj left) ht
        have hy := congrArg (fun H : OrdinaryTwoObjectCell.cell L ⟶ D ↦ H.obj right) ht
        change (originalIso C x y i u0 g0 f sq).hom.obj x = g0.obj left at hx
        change (originalIso C x y i u0 g0 f sq).hom.obj y = g0.obj right at hy
        rw [hx, hy]) = g0.map left right :=
  enriched_congr_map (t_originalIso C x y i u0 g0 f sq) left right

end
end DaggerRelativeOneCellPresentation
