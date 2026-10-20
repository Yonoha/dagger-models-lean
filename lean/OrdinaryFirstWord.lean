import DaggerModels.OrdinaryTwoObjectCell
import DaggerModels.SimplicialObjectAdjunctions
import OrdinaryAnodyneTensor

/-!
The first relative-word stage of one ordinary free cell attachment.
P1 is an SSet pushout only. Higher word stages and the complete enriched pushout
comparison are not asserted here.
-/

open CategoryTheory Limits MonoidalCategory HomotopicalAlgebra DaggerModels
open scoped SSet.modelCategoryQuillen

universe u

noncomputable section

namespace DaggerOrdinaryFirstWord

open OrdinaryTwoObjectCell
open TwoObjectDaggerGraph (Vertex left right)

variable {K L : SSet.{u}} (i : K ⟶ L) {C D : SimplicialCat.{u, u}}
  (x y : C.Obj) (u0 : K ⟶ (x ⟶[SSet] y))
  (f : C ⟶ D) (g : cell L ⟶ D)
  (sq : IsPushout (functor.map i) (fromData K C x y u0) g f)

include sq in
/-- The original variable-object square gives a bijection, including equal endpoints. -/
theorem objectMap_bijective : Function.Bijective f.obj := by
  letI : PreservesColimitsOfSize.{0, 0} SimplicialCat.objects.{u, u} :=
    SimplicialCat.objectsPreservesColimitsOfSize
  have top_id : SimplicialCat.objects.map (functor.map i) = 𝟙 Vertex.{u} := by
    funext v
    rcases v with ⟨v⟩
    cases v <;> rfl
  haveI : IsIso (SimplicialCat.objects.map (functor.map i)) := by
    rw [top_id]
    infer_instance
  haveI := (sq.map SimplicialCat.objects).isIso_inr_of_isIso
  exact (CategoryTheory.isIso_iff_bijective (SimplicialCat.objects.map f)).1 inferInstance

variable (a b : C.Obj)

/-- Old prefix, horn letter, and old suffix, with their original endpoints. -/
abbrev WordBoundary : SSet.{u} := ((a ⟶[SSet] x) ⊗ K) ⊗ (y ⟶[SSet] b)

/-- The corresponding word with one new letter. -/
abbrev WordObject : SSet.{u} := ((a ⟶[SSet] x) ⊗ L) ⊗ (y ⟶[SSet] b)

def wordMap : WordBoundary (K := K) x y a b ⟶ WordObject (L := L) x y a b :=
  ((a ⟶[SSet] x) ◁ i) ▷ (y ⟶[SSet] b)

/-- Replace the horn letter by u0, then use the two actual original compositions. -/
def attachMap : WordBoundary (K := K) x y a b ⟶ (a ⟶[SSet] b) :=
  (((a ⟶[SSet] x) ◁ u0) ▷ (y ⟶[SSet] b)) ≫
    (eComp SSet a x y ▷ (y ⟶[SSet] b)) ≫ eComp SSet a y b

abbrev P1 : SSet.{u} := pushout (attachMap x y u0 a b) (wordMap i x y a b)

def stageZero : (a ⟶[SSet] b) ⟶ P1 i x y u0 a b := pushout.inl _ _

def wordLeg : WordObject (L := L) x y a b ⟶ P1 i x y u0 a b := pushout.inr _ _

theorem stage_isPushout :
    IsPushout (attachMap x y u0 a b) (wordMap i x y a b)
      (stageZero i x y u0 a b) (wordLeg i x y u0 a b) :=
  IsPushout.of_hasPushout _ _

theorem wordMap_anodyne (hi : SSet.anodyneExtensions i) :
    SSet.anodyneExtensions (wordMap i x y a b) :=
  DaggerOrdinaryAnodyneTensor.whiskerRight _
    (DaggerOrdinaryAnodyneTensor.whiskerLeft i hi (a ⟶[SSet] x)) (y ⟶[SSet] b)

theorem stageZero_anodyne (hi : SSet.anodyneExtensions i) :
    SSet.anodyneExtensions (stageZero i x y u0 a b) :=
  MorphismProperty.of_isPushout (stage_isPushout i x y u0 a b)
    (wordMap_anodyne i x y a b hi)

theorem stageZero_trivialCofibration (hi : SSet.anodyneExtensions i) :
    trivialCofibrations SSet.{u} (stageZero i x y u0 a b) :=
  (DaggerOrdinaryAnodyneTensor.anodyne_iff_trivialCofibration _).1
    (stageZero_anodyne i x y u0 a b hi)

private theorem map_congr {E F : SimplicialCat.{u, u}} {p q : E ⟶ F}
    (h : p = q) (a b : E.Obj) : p.map a b ≫ eqToHom (by rw [h]) = q.map a b := by
  cases h
  simp

include sq in
theorem left_endpoint : g.obj left = f.obj x := by
  exact congrArg (fun h : cell K ⟶ D ↦ h.obj left) sq.w

include sq in
theorem right_endpoint : g.obj right = f.obj y := by
  exact congrArg (fun h : cell K ⟶ D ↦ h.obj right) sq.w

/-- Retain both actual object-equality transports from the original square. -/
def transportedEdge : L ⟶ (f.obj x ⟶[SSet] f.obj y) :=
  g.map left right ≫ eqToHom (by
    rw [left_endpoint i x y u0 f g sq, right_endpoint i x y u0 f g sq])

theorem transportedEdge_condition :
    i ≫ transportedEdge i x y u0 f g sq = u0 ≫ f.map x y := by
  have h := map_congr sq.w left right
  simpa only [transportedEdge, Category.assoc] using h

theorem transportedEdge_naturality {n m : SimplexCategoryᵒᵖ} (α : n ⟶ m) (l : L.obj n) :
    (transportedEdge i x y u0 f g sq).app m (L.map α l) =
      (f.obj x ⟶[SSet] f.obj y).map α ((transportedEdge i x y u0 f g sq).app n l) :=
  congrFun ((transportedEdge i x y u0 f g sq).naturality α) l

/-- Evaluate the one new letter using the transported original cell map. -/
def targetWord : WordObject (L := L) x y a b ⟶ (f.obj a ⟶[SSet] f.obj b) :=
  ((f.map a x ⊗ₘ transportedEdge i x y u0 f g sq) ⊗ₘ f.map y b) ≫
    (eComp SSet (f.obj a) (f.obj x) (f.obj y) ▷ (f.obj y ⟶[SSet] f.obj b)) ≫
      eComp SSet (f.obj a) (f.obj y) (f.obj b)

theorem targetWord_condition :
    attachMap x y u0 a b ≫ f.map a b = wordMap i x y a b ≫
      targetWord i x y u0 f g sq a b := by
  ext n p
  rcases p with ⟨⟨h, k⟩, v⟩
  have h₁ := congrFun (NatTrans.congr_app (f.map_comp a x y) n) (h, u0.app n k)
  have h₂ := congrFun (NatTrans.congr_app (f.map_comp a y b) n)
    ((eComp SSet a x y).app n (h, u0.app n k), v)
  have h₃ := congrFun (NatTrans.congr_app
    (transportedEdge_condition i x y u0 f g sq) n) k
  simp only [SSet.comp_app, types_comp_apply, SSet.tensorHom_app_apply] at h₁ h₂ h₃
  simp only [attachMap, wordMap, targetWord, SSet.comp_app, types_comp_apply,
    SSet.whiskerLeft_app_apply, SSet.whiskerRight_app_apply, SSet.tensorHom_app_apply]
  rw [h₂, h₁, h₃]

/-- The canonical first-stage map to the actual hom in the original enriched pushout. -/
def comparison : P1 i x y u0 a b ⟶ (f.obj a ⟶[SSet] f.obj b) :=
  pushout.desc (f.map a b) (targetWord i x y u0 f g sq a b)
    (targetWord_condition i x y u0 f g sq a b)

@[reassoc (attr := simp)]
theorem stageZero_comparison :
    stageZero i x y u0 a b ≫ comparison i x y u0 f g sq a b = f.map a b :=
  pushout.inl_desc _ _ _

@[reassoc (attr := simp)]
theorem wordLeg_comparison :
    wordLeg i x y u0 a b ≫ comparison i x y u0 f g sq a b =
      targetWord i x y u0 f g sq a b := pushout.inr_desc _ _ _

theorem generating_word_formula (n : SimplexCategoryᵒᵖ)
    (h : (a ⟶[SSet] x).obj n) (l : L.obj n) (v : (y ⟶[SSet] b).obj n) :
    (comparison i x y u0 f g sq a b).app n
      ((wordLeg i x y u0 a b).app n ((h, l), v)) =
    (eComp SSet (f.obj a) (f.obj y) (f.obj b)).app n
      ((eComp SSet (f.obj a) (f.obj x) (f.obj y)).app n
        ((f.map a x).app n h, (transportedEdge i x y u0 f g sq).app n l),
        (f.map y b).app n v) := by
  have e := congrFun (NatTrans.congr_app
    (wordLeg_comparison i x y u0 f g sq a b) n) ((h, l), v)
  simpa only [targetWord, SSet.comp_app, types_comp_apply, SSet.tensorHom_app_apply,
    SSet.whiskerRight_app_apply] using e

theorem comparison_naturality {n m : SimplexCategoryᵒᵖ} (α : n ⟶ m)
    (p : (P1 i x y u0 a b).obj n) :
    (comparison i x y u0 f g sq a b).app m ((P1 i x y u0 a b).map α p) =
      (f.obj a ⟶[SSet] f.obj b).map α
        ((comparison i x y u0 f g sq a b).app n p) :=
  congrFun ((comparison i x y u0 f g sq a b).naturality α) p

theorem generating_word_naturality {n m : SimplexCategoryᵒᵖ} (α : n ⟶ m)
    (h : (a ⟶[SSet] x).obj n) (l : L.obj n) (v : (y ⟶[SSet] b).obj n) :
    (f.obj a ⟶[SSet] f.obj b).map α
      ((targetWord i x y u0 f g sq a b).app n ((h, l), v)) =
    (targetWord i x y u0 f g sq a b).app m
      (((a ⟶[SSet] x).map α h, L.map α l), (y ⟶[SSet] b).map α v) :=
  (congrFun ((targetWord i x y u0 f g sq a b).naturality α) ((h, l), v)).symm

end DaggerOrdinaryFirstWord
