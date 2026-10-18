import RelativeOneCellPresentation
import OrdinaryReducedWords
import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono

/-! The actual original one-cell hom quotient has degreewise reduced-word normal forms.
Outside-subcomplex letters are used only at a fixed degree, never as a simplicial subobject. -/

open CategoryTheory DaggerModels
open DaggerRelativeOneCellPresentation DaggerOrdinaryReducedWords DaggerOrdinaryWordBoundary

universe u

namespace DaggerOrdinaryCellNormalizer

noncomputable section

variable (C : SimplicialCat.{u, u}) (x y : C.Obj) {L : SSet.{u}}
variable (A : L.Subcomplex) (uA : (A : SSet.{u}) ⟶ (x ⟶[SSet] y))

/-- A new original letter acts by its attaching arrow exactly when it lies in A. -/
def newAction (q : SimplexCategoryᵒᵖ) {a : C.Obj}
    (w : Reduced C x y A q a x) (l : L.obj q) : Reduced C x y A q a y := by
  classical
  exact if hl : l ∈ A.obj q then rightOld C x y A q w (uA.app q ⟨l, hl⟩)
    else rightNew C x y A q w l hl

/-- Act on an arbitrary reduced prefix using the literal original tagged edge. -/
def edgeAction (q : SimplexCategoryᵒᵖ) {a b c : C.Obj}
    (w : Reduced C x y A q a b) (e : (graphHom C x y (L := L) b c).obj q) :
    Reduced C x y A q a c := by
  cases e with
  | inl h => exact rightOld C x y A q w h
  | inr l =>
    have hb : b = x := l.property.1
    have hc : c = y := l.property.2
    subst b
    subst c
    exact newAction C x y A uA q w l.val

/-- Fold the existing actual snoc paths, retaining the arbitrary reduced prefix. -/
def act (q : SimplexCategoryᵒᵖ) {a b : C.Obj} (w : Reduced C x y A q a b) :
    {c : C.Obj} → Path C x y (L := L) q b c → Reduced C x y A q a c
  | _, .nil => w
  | _, .cons p e => edgeAction C x y A uA q (act q w p) e

theorem act_comp (q : SimplexCategoryᵒᵖ) {a b c d : C.Obj}
    (w : Reduced C x y A q a b) (p : Path C x y (L := L) q b c)
    (s : Path C x y (L := L) q c d) :
    act C x y A uA q w (p.comp s) = act C x y A uA q (act C x y A uA q w p) s := by
  induction s with
  | nil => rfl
  | cons s e ih =>
    change edgeAction C x y A uA q (act C x y A uA q w (p.comp s)) e = _
    rw [ih]
    rfl

@[simp] theorem act_oldPath (q : SimplexCategoryᵒᵖ) {a b c : C.Obj}
    (w : Reduced C x y A q a b) (h : (b ⟶[SSet] c).obj q) :
    act C x y A uA q w (oldPath C x y q h) = rightOld C x y A q w h := rfl

@[simp] theorem act_newPath (q : SimplexCategoryᵒᵖ) {a : C.Obj}
    (w : Reduced C x y A q a x) (l : L.obj q) :
    act C x y A uA q w (newPath C x y q l) = newAction C x y A uA q w l := rfl

/-- Each of the three original relations is invariant in every reduced left context. -/
theorem act_relation (q : SimplexCategoryᵒᵖ) {a b c : C.Obj}
    (w : Reduced C x y A q a b) {p p' : Path C x y (L := L) q b c}
    (h : Rel C x y A.ι uA q b c p p') :
    act C x y A uA q w p = act C x y A uA q w p' := by
  cases h with
  | oldId b => exact rightOld_id C x y A q w
  | oldComp h j =>
    rw [act_comp, act_oldPath, act_oldPath, act_oldPath]
    exact rightOld_assoc C x y A q w h j
  | attaching k =>
    rw [act_newPath, act_oldPath]
    change newAction C x y A uA q w k.val = rightOld C x y A q w (uA.app q k)
    simp only [newAction, dif_pos k.property]
    rfl

/-- Invariance under the exact original CompClosure, including both contexts. -/
theorem act_compClosure (q : SimplexCategoryᵒᵖ) {a b c : C.Obj}
    (w : Reduced C x y A q a b) {p p' : Path C x y (L := L) q b c}
    (h : HomRel.CompClosure
      (SimplicialCat.HomQuotient.degreeRel (relations C x y A.ι uA) q) p p') :
    act C x y A uA q w p = act C x y A uA q w p' := by
  rcases h with ⟨d, e, pre, m₁, m₂, suffix, h⟩
  change act C x y A uA q w (pre.comp (m₁.comp suffix)) =
    act C x y A uA q w (pre.comp (m₂.comp suffix))
  rw [act_comp, act_comp, act_comp, act_comp]
  rw [act_relation C x y A uA q (act C x y A uA q w pre) h]

def initial (q : SimplexCategoryᵒᵖ) (a : C.Obj) : Reduced C x y A q a a :=
  old C x y A q ((eId SSet a).app q PUnit.unit)

def normalizePath (q : SimplexCategoryᵒᵖ) {a b : C.Obj}
    (p : Path C x y (L := L) q a b) : Reduced C x y A q a b :=
  act C x y A uA q (initial C x y A q a) p

/-- Normalize the original HomObj, which is literally the original contextual Quot. -/
def normalize (q : SimplexCategoryᵒᵖ) (a b : C.Obj) :
    SimplicialCat.HomQuotient.HomObj (relations C x y A.ι uA) q a b →
      Reduced C x y A q a b :=
  Quot.lift (normalizePath C x y A uA q)
    (fun _ _ h ↦ act_compClosure C x y A uA q (initial C x y A q a) h)

@[simp] theorem normalize_mk (q : SimplexCategoryᵒᵖ) {a b : C.Obj}
    (p : Path C x y (L := L) q a b) :
    normalize C x y A uA q a b
      (SimplicialCat.HomQuotient.mk (relations C x y A.ι uA) q p) =
        normalizePath C x y A uA q p := rfl


/-- Decode every original raw word to the existing actual tagged path. -/
def decodeWord (q : SimplexCategoryᵒᵖ) : (n : ℕ) → (a b : C.Obj) →
    (Word C x y L n a b).obj q → Path C x y (L := L) q a b
  | 0, _, _, w => oldPath C x y q w
  | n + 1, _, b, w => (oldPath C x y q w.1.1).comp
      ((newPath C x y q w.1.2).comp (decodeWord q n y b w.2))


/-- The raw decoder respects every original simplex operator before taking the quotient. -/
theorem decodeWord_map {q q' : SimplexCategoryᵒᵖ} (α : q ⟶ q')
    (n : ℕ) (a b : C.Obj) (w : (Word C x y L n a b).obj q) :
    SimplicialColimitsFree.Paths.map (graph C x y (L := L)) α
      (decodeWord C x y q n a b w) =
        decodeWord C x y q' n a b ((Word C x y L n a b).map α w) := by
  induction n generalizing a with
  | zero => exact map_oldPath C x y α w
  | succ n ih =>
    simp only [decodeWord, SimplicialColimitsFree.Paths.map_pathComp,
      map_oldPath, map_newPath]
    rw [ih y w.2]
    rfl

/-- Evaluation of every original raw word in the same original quotient, at all degrees. -/
def wordEvaluation (n : ℕ) (a b : C.Obj) :
    Word C x y L n a b ⟶ SimplicialCat.HomQuotient.hom (relations C x y A.ι uA) a b where
  app q w := SimplicialCat.HomQuotient.mk (relations C x y A.ι uA) q
    (decodeWord C x y q n a b w)
  naturality q q' α := by
    funext w
    change SimplicialCat.HomQuotient.mk (relations C x y A.ι uA) q'
      (decodeWord C x y q' n a b ((Word C x y L n a b).map α w)) =
        SimplicialCat.HomQuotient.mk (relations C x y A.ι uA) q'
          (SimplicialColimitsFree.Paths.map _ α (decodeWord C x y q n a b w))
    rw [decodeWord_map]

def decode (q : SimplexCategoryᵒᵖ) {a b : C.Obj} (w : Reduced C x y A q a b) :
    Path C x y (L := L) q a b := decodeWord C x y q w.1 a b w.2.val

def decodeClass (q : SimplexCategoryᵒᵖ) {a b : C.Obj}
    (w : Reduced C x y A q a b) :
    SimplicialCat.HomQuotient.HomObj (relations C x y A.ι uA) q a b :=
  SimplicialCat.HomQuotient.mk (relations C x y A.ι uA) q (decode C x y A q w)

/-- Prepending an original old arrow and an outside-A letter to an original reduced tail. -/
def prepend (q : SimplexCategoryᵒᵖ) {a b : C.Obj} (h : (a ⟶[SSet] x).obj q)
    (l : L.obj q) (hl : l ∉ A.obj q) (w : Reduced C x y A q y b) :
    Reduced C x y A q a b :=
  ⟨w.1 + 1, ((h, l), w.2.val), fun hm ↦
    ((mem_boundary_succ C x y A w.1 a b q _).1 hm).elim hl w.2.property⟩

@[simp] theorem edgeAction_prepend (q : SimplexCategoryᵒᵖ) {a b c : C.Obj}
    (h : (a ⟶[SSet] x).obj q) (l : L.obj q) (hl : l ∉ A.obj q)
    (w : Reduced C x y A q y b) (e : (graphHom C x y (L := L) b c).obj q) :
    edgeAction C x y A uA q (prepend C x y A q h l hl w) e =
      prepend C x y A q h l hl (edgeAction C x y A uA q w e) := by
  classical
  rcases e with k | ⟨k, hb, hc⟩
  · rfl
  · subst b
    subst c
    change newAction C x y A uA q (prepend C x y A q h l hl w) k =
      prepend C x y A q h l hl (newAction C x y A uA q w k)
    by_cases hk : k ∈ A.obj q
    · simp only [newAction, dif_pos hk]
      rfl
    · simp only [newAction, dif_neg hk]
      rfl

theorem act_prepend (q : SimplexCategoryᵒᵖ) {a b c : C.Obj}
    (h : (a ⟶[SSet] x).obj q) (l : L.obj q) (hl : l ∉ A.obj q)
    (w : Reduced C x y A q y b) (p : Path C x y (L := L) q b c) :
    act C x y A uA q (prepend C x y A q h l hl w) p =
      prepend C x y A q h l hl (act C x y A uA q w p) := by
  induction p with
  | nil => rfl
  | cons p e ih =>
    change edgeAction C x y A uA q
      (act C x y A uA q (prepend C x y A q h l hl w) p) e = _
    rw [ih, edgeAction_prepend]
    rfl

@[simp] theorem normalize_oldPath (q : SimplexCategoryᵒᵖ) {a b : C.Obj}
    (h : (a ⟶[SSet] b).obj q) :
    normalizePath C x y A uA q (oldPath C x y q h) = old C x y A q h := by
  apply congrArg (Sigma.mk 0)
  apply Subtype.ext
  exact Category.id_comp (obj := SimplicialEnrichment.At C.Obj q) h

theorem normalize_decodeWord (q : SimplexCategoryᵒᵖ) (n : ℕ) (a b : C.Obj)
    (w : (Word C x y L n a b).obj q) (hw : w ∉ (Boundary C x y A n a b).obj q) :
    normalizePath C x y A uA q (decodeWord C x y q n a b w) = ⟨n, w, hw⟩ := by
  classical
  induction n generalizing a with
  | zero => exact normalize_oldPath C x y A uA q w
  | succ n ih =>
    have hl : w.1.2 ∉ A.obj q := fun hm ↦ hw
      ((mem_boundary_succ C x y A n a b q w).2 (Or.inl hm))
    have ht : w.2 ∉ (Boundary C x y A n y b).obj q := fun hm ↦ hw
      ((mem_boundary_succ C x y A n a b q w).2 (Or.inr hm))
    change act C x y A uA q (initial C x y A q a)
      ((oldPath C x y q w.1.1).comp
        ((newPath C x y q w.1.2).comp (decodeWord C x y q n y b w.2))) = _
    rw [act_comp]
    change act C x y A uA q
      (normalizePath C x y A uA q (oldPath C x y q w.1.1)) _ = _
    rw [normalize_oldPath, act_comp, act_newPath]
    simp only [newAction, dif_neg hl]
    change act C x y A uA q
      (prepend C x y A q w.1.1 w.1.2 hl (initial C x y A q y)) _ = _
    rw [act_prepend]
    change prepend C x y A q w.1.1 w.1.2 hl
      (normalizePath C x y A uA q (decodeWord C x y q n y b w.2)) = _
    rw [ih y w.2 ht]
    rfl

@[simp] theorem normalize_decodeClass (q : SimplexCategoryᵒᵖ) {a b : C.Obj}
    (w : Reduced C x y A q a b) :
    normalize C x y A uA q a b (decodeClass C x y A uA q w) = w :=
  normalize_decodeWord C x y A uA q w.1 a b w.2.val w.2.property


/-- Concatenation in the existing contextual hom quotient. -/
theorem mk_comp (q : SimplexCategoryᵒᵖ) {a b c : C.Obj}
    (p : Path C x y (L := L) q a b) (s : Path C x y (L := L) q b c) :
    SimplicialCat.HomQuotient.mk (relations C x y A.ι uA) q (p.comp s) =
      CategoryTheory.Quotient.comp
        (SimplicialCat.HomQuotient.degreeRel (relations C x y A.ι uA) q)
        (SimplicialCat.HomQuotient.mk (relations C x y A.ι uA) q p)
        (SimplicialCat.HomQuotient.mk (relations C x y A.ι uA) q s) := rfl

theorem mk_comp_congr (q : SimplexCategoryᵒᵖ) {a b c : C.Obj}
    {p p' : Path C x y (L := L) q a b} {s s' : Path C x y (L := L) q b c}
    (hp : SimplicialCat.HomQuotient.mk (relations C x y A.ι uA) q p =
      SimplicialCat.HomQuotient.mk (relations C x y A.ι uA) q p')
    (hs : SimplicialCat.HomQuotient.mk (relations C x y A.ι uA) q s =
      SimplicialCat.HomQuotient.mk (relations C x y A.ι uA) q s') :
    SimplicialCat.HomQuotient.mk (relations C x y A.ι uA) q (p.comp s) =
      SimplicialCat.HomQuotient.mk (relations C x y A.ι uA) q (p'.comp s') := by
  rw [mk_comp, mk_comp, hp, hs]

theorem decode_appendOld (q : SimplexCategoryᵒᵖ) (n : ℕ) (a b c : C.Obj)
    (w : (Word C x y L n a b).obj q) (h : (b ⟶[SSet] c).obj q) :
    SimplicialCat.HomQuotient.mk (relations C x y A.ι uA) q
      (decodeWord C x y q n a c (appendOld C x y L q n a b c w h)) =
        SimplicialCat.HomQuotient.mk (relations C x y A.ι uA) q
          ((decodeWord C x y q n a b w).comp (oldPath C x y q h)) := by
  induction n generalizing a with
  | zero =>
    exact (SimplicialCat.HomQuotient.sound (relations C x y A.ι uA) q (Rel.oldComp w h)).symm
  | succ n ih =>
    change SimplicialCat.HomQuotient.mk (relations C x y A.ι uA) q
      ((oldPath C x y q w.1.1).comp ((newPath C x y q w.1.2).comp
        (decodeWord C x y q n y c (appendOld C x y L q n y b c w.2 h)))) = _
    simp only [decodeWord, Quiver.Path.comp_assoc]
    apply mk_comp_congr C x y A uA q rfl
    apply mk_comp_congr C x y A uA q rfl
    exact ih y w.2

theorem decode_appendNew (q : SimplexCategoryᵒᵖ) (n : ℕ) (a : C.Obj)
    (w : (Word C x y L n a x).obj q) (l : L.obj q) :
    SimplicialCat.HomQuotient.mk (relations C x y A.ι uA) q
      (decodeWord C x y q (n + 1) a y (appendNew C x y L q n a w l)) =
        SimplicialCat.HomQuotient.mk (relations C x y A.ι uA) q
          ((decodeWord C x y q n a x w).comp (newPath C x y q l)) := by
  induction n generalizing a with
  | zero =>
    change SimplicialCat.HomQuotient.mk (relations C x y A.ι uA) q ((oldPath C x y q w).comp
      ((newPath C x y q l).comp (oldPath C x y q ((eId SSet y).app q PUnit.unit)))) = _
    apply mk_comp_congr C x y A uA q rfl
    change SimplicialCat.HomQuotient.mk (relations C x y A.ι uA) q
      ((newPath C x y q l).comp (oldPath C x y q ((eId SSet y).app q PUnit.unit))) =
        SimplicialCat.HomQuotient.mk (relations C x y A.ι uA) q ((newPath C x y q l).comp .nil)
    exact mk_comp_congr C x y A uA q rfl
      (SimplicialCat.HomQuotient.sound (relations C x y A.ι uA) q (Rel.oldId y))
  | succ n ih =>
    change SimplicialCat.HomQuotient.mk (relations C x y A.ι uA) q ((oldPath C x y q w.1.1).comp
      ((newPath C x y q w.1.2).comp
        (decodeWord C x y q (n + 1) y y (appendNew C x y L q n y w.2 l)))) = _
    simp only [decodeWord, Quiver.Path.comp_assoc]
    apply mk_comp_congr C x y A uA q rfl
    apply mk_comp_congr C x y A uA q rfl
    exact ih y w.2

theorem decode_edgeAction (q : SimplexCategoryᵒᵖ) {a b c : C.Obj}
    (w : Reduced C x y A q a b) (e : (graphHom C x y (L := L) b c).obj q) :
    decodeClass C x y A uA q (edgeAction C x y A uA q w e) =
      SimplicialCat.HomQuotient.mk (relations C x y A.ι uA) q
        ((decode C x y A q w).cons e) := by
  classical
  rcases e with h | ⟨l, hb, hc⟩
  · exact decode_appendOld C x y A uA q w.1 a b c w.2.val h
  · subst b
    subst c
    change decodeClass C x y A uA q (newAction C x y A uA q w l) = _
    by_cases hl : l ∈ A.obj q
    · simp only [newAction, dif_pos hl]
      trans SimplicialCat.HomQuotient.mk (relations C x y A.ι uA) q
        ((decode C x y A q w).comp (oldPath C x y q (uA.app q ⟨l, hl⟩)))
      · exact decode_appendOld C x y A uA q w.1 a x y w.2.val (uA.app q ⟨l, hl⟩)
      · exact mk_comp_congr C x y A uA q rfl
          (SimplicialCat.HomQuotient.sound (relations C x y A.ι uA) q
            (Rel.attaching (C := C) (x := x) (y := y)
            (i := A.ι) (u0 := uA) (q := q) ⟨l, hl⟩)).symm
    · simp only [newAction, dif_neg hl]
      exact decode_appendNew C x y A uA q w.1 a w.2.val l

theorem decode_normalizePath (q : SimplexCategoryᵒᵖ) {a b : C.Obj}
    (p : Path C x y (L := L) q a b) :
    decodeClass C x y A uA q (normalizePath C x y A uA q p) =
      SimplicialCat.HomQuotient.mk (relations C x y A.ι uA) q p := by
  induction p with
  | nil => exact SimplicialCat.HomQuotient.sound (relations C x y A.ι uA) q (Rel.oldId a)
  | cons p e ih =>
    change decodeClass C x y A uA q
      (edgeAction C x y A uA q (normalizePath C x y A uA q p) e) = _
    rw [decode_edgeAction]
    simpa only [edgePath, SimplicialColimitsFree.Paths.inclusion,
      Quiver.Path.comp_toPath_eq_cons] using
      mk_comp_congr C x y A uA q (s := edgePath C x y q e)
        (s' := edgePath C x y q e) ih rfl

@[simp] theorem decodeClass_normalize (q : SimplexCategoryᵒᵖ) (a b : C.Obj)
    (z : SimplicialCat.HomQuotient.HomObj (relations C x y A.ι uA) q a b) :
    decodeClass C x y A uA q (normalize C x y A uA q a b z) = z := by
  induction z using Quot.inductionOn with
  | h p => exact decode_normalizePath C x y A uA q p

/-- A full equivalence with the original reduced words at every original endpoint and degree. -/
def homEquiv (q : SimplexCategoryᵒᵖ) (a b : C.Obj) :
    SimplicialCat.HomQuotient.HomObj (relations C x y A.ι uA) q a b ≃
      Reduced C x y A q a b where
  toFun := normalize C x y A uA q a b
  invFun := decodeClass C x y A uA q
  left_inv := decodeClass_normalize C x y A uA q a b
  right_inv := normalize_decodeClass C x y A uA q

@[simp] theorem normalize_oldMap (q : SimplexCategoryᵒᵖ) (a b : C.Obj)
    (h : (a ⟶[SSet] b).obj q) :
    normalize C x y A uA q a b ((v C x y A.ι uA).map a b |>.app q h) =
      old C x y A q h := normalize_oldPath C x y A uA q h

theorem oldMap_injective (q : SimplexCategoryᵒᵖ) (a b : C.Obj) :
    Function.Injective ((v C x y A.ι uA).map a b |>.app q) := by
  intro h k hk
  apply old_injective C x y A q a b
  simpa only [normalize_oldMap] using congrArg (normalize C x y A uA q a b) hk

instance oldMap_mono (a b : C.Obj) : Mono ((v C x y A.ι uA).map a b) :=
  (NatTrans.mono_iff_mono_app _).2 (fun q ↦
    (mono_iff_injective _).2 (oldMap_injective C x y A uA q a b))

end

end DaggerOrdinaryCellNormalizer
