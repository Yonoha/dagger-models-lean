import SSetSM7
import OrdinaryAnodyneTensor

/-! Exact two-pushout anodyne section for an arbitrary original first Hom stage. -/

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

universe u

namespace DaggerAmalgamFirstStage

noncomputable section

variable {A B X P : SSet.{u}}

/-- Every actual point map is mono in every simplicial degree. -/
lemma point_mono (e : 𝟙_ SSet.{u} ⟶ X) : Mono e := by
  rw [NatTrans.mono_iff_mono_app]
  intro n
  apply (CategoryTheory.mono_iff_injective _).2
  intro z w _
  cases z
  cases w
  rfl

/-- The original inclusion at the specified right coordinate. -/
def atRight (A : SSet.{u}) (e : 𝟙_ SSet.{u} ⟶ X) : A ⟶ A ⊗ X :=
  (ρ_ A).inv ≫ A ◁ e

/-- The original inclusion at the specified left coordinate. -/
def atLeft (a : 𝟙_ SSet.{u} ⟶ A) (X : SSet.{u}) : X ⟶ A ⊗ X :=
  (λ_ X).inv ≫ a ▷ X

@[simp] theorem atRight_app (e : 𝟙_ SSet.{u} ⟶ X)
    (n : SimplexCategoryᵒᵖ) (z : A.obj n) :
    (atRight A e).app n z = (z, e.app n PUnit.unit) := rfl

@[simp] theorem atLeft_app (a : 𝟙_ SSet.{u} ⟶ A)
    (n : SimplexCategoryᵒᵖ) (z : X.obj n) :
    (atLeft a X).app n z = (a.app n PUnit.unit, z) := rfl

/-- Actual full two-piece pushout-product domain. -/
def domain (a : 𝟙_ SSet.{u} ⟶ A) (e : 𝟙_ SSet.{u} ⟶ X) :
    SSet.PushoutTensor a e := DaggerSSetSM7.pushoutTensor a e

/-- The first pushout uses the actual composite a followed by m. -/
def first (a : 𝟙_ SSet.{u} ⟶ A) (e : 𝟙_ SSet.{u} ⟶ X) (m : A ⟶ B) : SSet.{u} :=
  pushout (a ≫ m) e

/-- The complete map of the domain's two pieces into the first pushout. -/
def domainToFirst (a : 𝟙_ SSet.{u} ⟶ A) (e : 𝟙_ SSet.{u} ⟶ X) (m : A ⟶ B) :
    (domain a e).pt ⟶ first a e m :=
  (domain a e).isPushout.desc
    ((ρ_ A).hom ≫ m ≫ pushout.inl (a ≫ m) e)
    ((λ_ X).hom ≫ pushout.inr (a ≫ m) e) (by
      ext n z
      rcases z with ⟨⟨⟩, ⟨⟩⟩
      exact congrFun (NatTrans.congr_app (pushout.condition (f := a ≫ m) (g := e)) n)
        PUnit.unit)

@[reassoc (attr := simp)] theorem domain_inl_first
    (a : 𝟙_ SSet.{u} ⟶ A) (e : 𝟙_ SSet.{u} ⟶ X) (m : A ⟶ B) :
    (domain a e).inl ≫ domainToFirst a e m =
      (ρ_ A).hom ≫ m ≫ pushout.inl (a ≫ m) e := by simp [domainToFirst]

@[reassoc (attr := simp)] theorem domain_inr_first
    (a : 𝟙_ SSet.{u} ⟶ A) (e : 𝟙_ SSet.{u} ⟶ X) (m : A ⟶ B) :
    (domain a e).inr ≫ domainToFirst a e m =
      (λ_ X).hom ≫ pushout.inr (a ≫ m) e := by simp [domainToFirst]

variable (a : 𝟙_ SSet.{u} ⟶ A) (e : 𝟙_ SSet.{u} ⟶ X) (m : A ⟶ B)
  (i : B ⟶ P) (k : A ⊗ X ⟶ P) (sq : IsPushout m (atRight A e) i k)

/-- The section uses the actual original product leg. -/
def sectionMap : X ⟶ P := atLeft a X ≫ k

/-- The complete first-pushout cocone into the original apex. -/
def firstToOriginal : first a e m ⟶ P :=
  pushout.desc i (sectionMap a k) (by
    ext n z
    cases z
    exact congrFun (NatTrans.congr_app sq.w n) (a.app n PUnit.unit))

@[reassoc (attr := simp)] theorem first_left_original :
    pushout.inl (a ≫ m) e ≫ firstToOriginal a e m i k sq = i := by
  simp [firstToOriginal]

@[reassoc (attr := simp)] theorem first_right_original :
    pushout.inr (a ≫ m) e ≫ firstToOriginal a e m i k sq = sectionMap a k := by
  simp [firstToOriginal]

/-- Both domain pieces commute into the same original pushout. -/
theorem second_comm :
    domainToFirst a e m ≫ firstToOriginal a e m i k sq = (domain a e).ι ≫ k := by
  apply (domain a e).isPushout.hom_ext
  · simpa [Category.assoc, firstToOriginal, atRight] using
      congrArg (fun f ↦ (ρ_ A).hom ≫ f) sq.w
  · simp [firstToOriginal, sectionMap, atLeft, Category.assoc]

variable {Y : SSet.{u}} (f : first a e m ⟶ Y) (g : A ⊗ X ⟶ Y)
  (w : domainToFirst a e m ≫ f = (domain a e).ι ≫ g)

/-- An arbitrary cocone's original relation, recovered from the FULL first piece. -/
theorem original_relation (w : domainToFirst a e m ≫ f = (domain a e).ι ≫ g) :
    m ≫ (pushout.inl (a ≫ m) e ≫ f) = atRight A e ≫ g := by
  have h := congrArg (fun t ↦ (domain a e).inl ≫ t) w
  simpa [Category.assoc, atRight] using congrArg (fun t ↦ (ρ_ A).inv ≫ t) h

/-- The second piece forces its entire X map, not only its chosen point. -/
theorem forced_X_relation (w : domainToFirst a e m ≫ f = (domain a e).ι ≫ g) :
    pushout.inr (a ≫ m) e ≫ f = atLeft a X ≫ g := by
  have h := congrArg (fun t ↦ (domain a e).inr ≫ t) w
  simpa [Category.assoc, atLeft] using congrArg (fun t ↦ (λ_ X).inv ≫ t) h

/-- Desc for every target and every full two-piece cocone. -/
def secondDesc : P ⟶ Y :=
  sq.desc (pushout.inl (a ≫ m) e ≫ f) g (original_relation a e m f g w)

@[reassoc (attr := simp)] theorem secondDesc_right :
    k ≫ secondDesc a e m i k sq f g w = g := by simp [secondDesc]

@[reassoc (attr := simp)] theorem secondDesc_left :
    firstToOriginal a e m i k sq ≫ secondDesc a e m i k sq f g w = f := by
  apply pushout.hom_ext
  · simp [secondDesc]
  · simp [sectionMap, secondDesc, Category.assoc]
    exact (forced_X_relation a e m f g w).symm

/-- Arbitrary-target uniqueness uses BOTH original legs. -/
theorem secondDesc_unique (t : P ⟶ Y)
    (hl : firstToOriginal a e m i k sq ≫ t = f) (hr : k ≫ t = g) :
    t = secondDesc a e m i k sq f g w := by
  apply sq.hom_ext
  · simpa [secondDesc, Category.assoc] using
      congrArg (fun z ↦ pushout.inl (a ≫ m) e ≫ z) hl
  · simpa [secondDesc] using hr

/-- Complete second-stage UP on the original P; no apex replacement is assumed. -/
def secondIsPushout :
    IsPushout (domainToFirst a e m) (domain a e).ι
      (firstToOriginal a e m i k sq) k :=
  IsPushout.of_isColimit (PushoutCocone.IsColimit.mk (second_comm a e m i k sq)
    (fun s ↦ secondDesc a e m i k sq s.inl s.inr s.condition)
    (fun s ↦ secondDesc_left a e m i k sq s.inl s.inr s.condition)
    (fun s ↦ secondDesc_right a e m i k sq s.inl s.inr s.condition)
    (fun s t hl hr ↦ secondDesc_unique a e m i k sq s.inl s.inr s.condition t hl hr))

/-- Both inverse laws come from the complete UP, with both full original legs. -/
def secondIso :
    pushout (domainToFirst a e m) (domain a e).ι ≅ P :=
  (secondIsPushout a e m i k sq).isoPushout.symm

@[reassoc (attr := simp)] theorem secondIso_first :
    pushout.inl (domainToFirst a e m) (domain a e).ι ≫
      (secondIso a e m i k sq).hom = firstToOriginal a e m i k sq := by
  simp [secondIso]

@[reassoc (attr := simp)] theorem secondIso_product :
    pushout.inr (domainToFirst a e m) (domain a e).ι ≫
      (secondIso a e m i k sq).hom = k := by simp [secondIso]

/-- The original B leg is retained through both actual chosen pushouts. -/
@[reassoc] theorem secondIso_B :
    (pushout.inl (a ≫ m) e ≫ pushout.inl (domainToFirst a e m) (domain a e).ι) ≫
      (secondIso a e m i k sq).hom = i := by simp [Category.assoc]

/-- The point on the product is the actual section through both stages. -/
theorem section_two_stages :
    sectionMap a k = pushout.inr (a ≫ m) e ≫ firstToOriginal a e m i k sq := by simp

include sq in
/-- The full chosen section is anodyne with no hypothesis on m(a) being a unit. -/
theorem section_anodyne (ha : SSet.anodyneExtensions a)
    (hb : SSet.anodyneExtensions (a ≫ m)) : SSet.anodyneExtensions (sectionMap a k) := by
  letI := point_mono e
  have hd : SSet.anodyneExtensions (domain a e).ι :=
    SSet.anodyneExtensions.pushoutTensorι₁ (domain a e) ha
  have hfirst : SSet.anodyneExtensions (pushout.inr (a ≫ m) e) :=
    MorphismProperty.of_isPushout (IsPushout.of_hasPushout (a ≫ m) e).flip hb
  have hsecond : SSet.anodyneExtensions (firstToOriginal a e m i k sq) :=
    MorphismProperty.of_isPushout (secondIsPushout a e m i k sq) hd
  rw [section_two_stages a e m i k sq]
  exact SSet.anodyneExtensions.comp_mem _ _ hfirst hsecond

/-- Original collapse: its B leg is constant e and its product leg is projection. -/
def collapse : P ⟶ X :=
  sq.desc (toUnit B ≫ e) (snd A X) (by ext n z; rfl)

@[reassoc (attr := simp)] theorem collapse_B :
    i ≫ collapse e m i k sq = toUnit B ≫ e := by simp [collapse]

@[reassoc (attr := simp)] theorem collapse_product :
    k ≫ collapse e m i k sq = snd A X := by simp [collapse]

/-- The same sectionMap and the same collapse compose strictly to the identity. -/
@[simp] theorem section_collapse :
    sectionMap a k ≫ collapse e m i k sq = 𝟙 X := by
  simp [sectionMap, collapse, atLeft, Category.assoc]

/-- Weak equivalence retains the literal realization/singular predicate. -/
theorem collapse_geometric (ha : SSet.anodyneExtensions a)
    (hb : SSet.anodyneExtensions (a ≫ m)) :
    SSet.KanComplex.W (TopCat.toSSet.map (SSet.toTop.map (collapse e m i k sq))) := by
  have hs := section_anodyne a e m i k sq ha hb
  letI : WeakEquivalence (sectionMap a k) :=
    ((mem_trivialCofibrations_iff _).1
      ((DaggerOrdinaryAnodyneTensor.anodyne_iff_trivialCofibration _).1 hs)).2
  haveI : WeakEquivalence (sectionMap a k ≫ collapse e m i k sq) := by
    rw [section_collapse]
    infer_instance
  letI := weakEquivalence_of_precomp (sectionMap a k) (collapse e m i k sq)
  exact (DaggerModels.KanQuillenReuse.weakEquivalence_iff_geometric _).1 inferInstance

/-- A selected point of an original geometrically weakly contractible Hom is anodyne. -/
theorem point_anodyne {Y : SSet.{u}} (z : 𝟙_ SSet.{u} ⟶ Y)
    (hY : SSet.KanComplex.W (TopCat.toSSet.map (SSet.toTop.map (toUnit Y)))) :
    SSet.anodyneExtensions z := by
  letI := point_mono z
  letI : Cofibration z := SSet.modelCategoryQuillen.cofibration_of_mono z
  letI : WeakEquivalence (toUnit Y) :=
    (DaggerModels.KanQuillenReuse.weakEquivalence_iff_geometric _).2 hY
  haveI : WeakEquivalence (z ≫ toUnit Y) := by
    have h : z ≫ toUnit Y = 𝟙 _ := isTerminalTensorUnit.hom_ext _ _
    rw [h]
    infer_instance
  letI := weakEquivalence_of_postcomp z (toUnit Y)
  exact (DaggerOrdinaryAnodyneTensor.anodyne_iff_trivialCofibration z).2
    (mem_trivialCofibrations z)

/-- Actual arbitrary-factor inclusion at the chosen point. -/
theorem atLeft_anodyne (X : SSet.{u}) (ha : SSet.anodyneExtensions a) :
    SSet.anodyneExtensions (atLeft a X) :=
  SSet.anodyneExtensions.comp_mem _ _ (SSet.anodyneExtensions.of_isIso _)
    (DaggerOrdinaryAnodyneTensor.whiskerRight a ha X)

/-- The actual pair of the two selected vertices, in the original order. -/
def pointPair {L R : SSet.{u}} (l : 𝟙_ SSet.{u} ⟶ L) (r : 𝟙_ SSet.{u} ⟶ R) :
    𝟙_ SSet.{u} ⟶ L ⊗ R := r ≫ atLeft l R

@[simp] theorem pointPair_app {L R : SSet.{u}}
    (l : 𝟙_ SSet.{u} ⟶ L) (r : 𝟙_ SSet.{u} ⟶ R) (n : SimplexCategoryᵒᵖ) :
    (pointPair l r).app n PUnit.unit = (l.app n PUnit.unit, r.app n PUnit.unit) := rfl

theorem pointPair_anodyne {L R : SSet.{u}}
    (l : 𝟙_ SSet.{u} ⟶ L) (r : 𝟙_ SSet.{u} ⟶ R)
    (hl : SSet.anodyneExtensions l) (hr : SSet.anodyneExtensions r) :
    SSet.anodyneExtensions (pointPair l r) :=
  SSet.anodyneExtensions.comp_mem _ _ hr (atLeft_anodyne l R hl)

/-- The exact associator and braiding for the original B10, X, B01 ordering. -/
def orderIso (L R X : SSet.{u}) : (L ⊗ R) ⊗ X ≅ L ⊗ (X ⊗ R) :=
  (α_ L R X) ≪≫ MonoidalCategory.whiskerLeftIso L (β_ R X)

@[simp] theorem orderIso_hom_app (L R X : SSet.{u}) (n : SimplexCategoryᵒᵖ)
    (z : ((L ⊗ R) ⊗ X).obj n) :
    (orderIso L R X).hom.app n z = (z.1.1, (z.2, z.1.2)) := rfl

@[simp] theorem orderIso_inv_app (L R X : SSet.{u}) (n : SimplexCategoryᵒᵖ)
    (z : (L ⊗ (X ⊗ R)).obj n) :
    (orderIso L R X).inv.app n z = ((z.1, z.2.2), z.2.1) := rfl

/-- Every original unit-coordinate map is preserved, in all simplicial degrees. -/
@[reassoc] theorem orderIso_unit (L R : SSet.{u}) :
    atRight (L ⊗ R) e ≫ (orderIso L R X).hom = L ◁ atLeft e R := by
  apply NatTrans.ext
  funext n z
  rfl

/-- The actual ordered pushout gives the original generic square with identical other legs. -/
def orderedIsPushout {L R : SSet.{u}} (m : L ⊗ R ⟶ B)
    (i : B ⟶ P) (k : L ⊗ (X ⊗ R) ⟶ P)
    (sq : IsPushout m (L ◁ atLeft e R) i k) :
    IsPushout m (atRight (L ⊗ R) e) i ((orderIso L R X).hom ≫ k) :=
  sq.of_iso (Iso.refl _) (Iso.refl _) (orderIso L R X).symm (Iso.refl _)
    (by simp) (by apply NatTrans.ext; funext n z; rfl) (by simp) (by simp)

/-- The SAME section in the original ordered product, with arbitrary composition m. -/
theorem ordered_section_anodyne {L R : SSet.{u}}
    (l : 𝟙_ SSet.{u} ⟶ L) (r : 𝟙_ SSet.{u} ⟶ R) (m : L ⊗ R ⟶ B)
    (i : B ⟶ P) (k : L ⊗ (X ⊗ R) ⟶ P)
    (sq : IsPushout m (L ◁ atLeft e R) i k)
    (hl : SSet.anodyneExtensions l) (hr : SSet.anodyneExtensions r)
    (hb : SSet.anodyneExtensions (pointPair l r ≫ m)) :
    SSet.anodyneExtensions
      (atLeft (pointPair l r) X ≫ (orderIso L R X).hom ≫ k) :=
  section_anodyne (pointPair l r) e m i _ (orderedIsPushout e m i k sq)
    (pointPair_anodyne l r hl hr) hb

/-- The same permutation with the original left-associated middle product. -/
def middleIso (L R X : SSet.{u}) : (L ⊗ R) ⊗ X ≅ (L ⊗ X) ⊗ R :=
  orderIso L R X ≪≫ (α_ L X R).symm

@[simp] theorem middleIso_hom_app (L R X : SSet.{u}) (n : SimplexCategoryᵒᵖ)
    (z : ((L ⊗ R) ⊗ X).obj n) :
    (middleIso L R X).hom.app n z = ((z.1.1, z.2), z.1.2) := rfl

@[simp] theorem middleIso_inv_app (L R X : SSet.{u}) (n : SimplexCategoryᵒᵖ)
    (z : ((L ⊗ X) ⊗ R).obj n) :
    (middleIso L R X).inv.app n z = ((z.1.1, z.2), z.1.2) := rfl

/-- The original middle insertion preserves each original outside factor. -/
@[reassoc] theorem middleIso_unit (L R : SSet.{u}) :
    atRight (L ⊗ R) e ≫ (middleIso L R X).hom = atRight L e ▷ R := by
  apply NatTrans.ext
  funext n z
  rfl

/-- Full original pushout transport, retaining its composition, apex and BOTH legs. -/
def middleIsPushout {L R : SSet.{u}} (m : L ⊗ R ⟶ B)
    (i : B ⟶ P) (k : (L ⊗ X) ⊗ R ⟶ P)
    (sq : IsPushout m (atRight L e ▷ R) i k) :
    IsPushout m (atRight (L ⊗ R) e) i ((middleIso L R X).hom ≫ k) :=
  sq.of_iso (Iso.refl _) (Iso.refl _) (middleIso L R X).symm (Iso.refl _)
    (by simp) (by apply NatTrans.ext; funext n z; rfl) (by simp) (by simp)

/-- Geometric L/R/B contractibility suffices at the ACTUAL composite point in B. -/
theorem middle_section_anodyne {L R : SSet.{u}}
    (l : 𝟙_ SSet.{u} ⟶ L) (r : 𝟙_ SSet.{u} ⟶ R) (m : L ⊗ R ⟶ B)
    (i : B ⟶ P) (k : (L ⊗ X) ⊗ R ⟶ P)
    (sq : IsPushout m (atRight L e ▷ R) i k)
    (hL : SSet.KanComplex.W (TopCat.toSSet.map (SSet.toTop.map (toUnit L))))
    (hR : SSet.KanComplex.W (TopCat.toSSet.map (SSet.toTop.map (toUnit R))))
    (hB : SSet.KanComplex.W (TopCat.toSSet.map (SSet.toTop.map (toUnit B)))) :
    SSet.anodyneExtensions
      (atLeft (pointPair l r) X ≫ (middleIso L R X).hom ≫ k) :=
  section_anodyne (pointPair l r) e m i _ (middleIsPushout e m i k sq)
    (pointPair_anodyne l r (point_anodyne l hL) (point_anodyne r hR))
    (point_anodyne (pointPair l r ≫ m) hB)

/-- The same original collapse on the left-associated original product square. -/
def middleCollapse {L R : SSet.{u}} (m : L ⊗ R ⟶ B)
    (i : B ⟶ P) (k : (L ⊗ X) ⊗ R ⟶ P)
    (sq : IsPushout m (atRight L e ▷ R) i k) : P ⟶ X :=
  collapse e m i _ (middleIsPushout e m i k sq)

@[reassoc (attr := simp)] theorem middleCollapse_B {L R : SSet.{u}}
    (m : L ⊗ R ⟶ B) (i : B ⟶ P) (k : (L ⊗ X) ⊗ R ⟶ P)
    (sq : IsPushout m (atRight L e ▷ R) i k) :
    i ≫ middleCollapse e m i k sq = toUnit B ≫ e := by simp [middleCollapse]

/-- The product projection retains all degrees and the original middle coordinate. -/
@[reassoc] theorem middleCollapse_product {L R : SSet.{u}}
    (m : L ⊗ R ⟶ B) (i : B ⟶ P) (k : (L ⊗ X) ⊗ R ⟶ P)
    (sq : IsPushout m (atRight L e ▷ R) i k) :
    k ≫ middleCollapse e m i k sq = fst (L ⊗ X) R ≫ snd L X := by
  rw [← cancel_epi (middleIso L R X).hom]
  change (middleIso L R X).hom ≫ k ≫
    collapse e m i _ (middleIsPushout e m i k sq) = _
  rw [← Category.assoc, collapse_product]
  apply NatTrans.ext
  funext n z
  rfl

/-- The exact original middle-coordinate collapse is a geometric weak equivalence. -/
theorem middleCollapse_geometric {L R : SSet.{u}}
    (l : 𝟙_ SSet.{u} ⟶ L) (r : 𝟙_ SSet.{u} ⟶ R) (m : L ⊗ R ⟶ B)
    (i : B ⟶ P) (k : (L ⊗ X) ⊗ R ⟶ P)
    (sq : IsPushout m (atRight L e ▷ R) i k)
    (hL : SSet.KanComplex.W (TopCat.toSSet.map (SSet.toTop.map (toUnit L))))
    (hR : SSet.KanComplex.W (TopCat.toSSet.map (SSet.toTop.map (toUnit R))))
    (hB : SSet.KanComplex.W (TopCat.toSSet.map (SSet.toTop.map (toUnit B)))) :
    SSet.KanComplex.W (TopCat.toSSet.map (SSet.toTop.map (middleCollapse e m i k sq))) :=
  collapse_geometric (pointPair l r) e m i _ (middleIsPushout e m i k sq)
    (pointPair_anodyne l r (point_anodyne l hL) (point_anodyne r hR))
    (point_anodyne (pointPair l r ≫ m) hB)

/-- Any supplied comparison with BOTH original legs is the same original collapse. -/
theorem collapse_unique (q : P ⟶ X) (hi : i ≫ q = toUnit B ≫ e)
    (hk : k ≫ q = snd A X) : q = collapse e m i k sq :=
  sq.hom_ext (hi.trans (collapse_B e m i k sq).symm)
    (hk.trans (collapse_product e m i k sq).symm)

include sq in
/-- The actual supplied comparison, rather than a replacement map, has the section identity. -/
theorem supplied_section_identity (q : P ⟶ X) (hi : i ≫ q = toUnit B ≫ e)
    (hk : k ≫ q = snd A X) : sectionMap a k ≫ q = 𝟙 X := by
  rw [collapse_unique e m i k sq q hi hk]
  exact section_collapse a e m i k sq

include sq in
/-- The actual supplied comparison retains the same original geometric W predicate. -/
theorem supplied_collapse_geometric (q : P ⟶ X) (hi : i ≫ q = toUnit B ≫ e)
    (hk : k ≫ q = snd A X) (ha : SSet.anodyneExtensions a)
    (hb : SSet.anodyneExtensions (a ≫ m)) :
    SSet.KanComplex.W (TopCat.toSSet.map (SSet.toTop.map q)) := by
  rw [collapse_unique e m i k sq q hi hk]
  exact collapse_geometric a e m i k sq ha hb

/-- An arbitrary given comparison in original middle coordinates is unchanged. -/
theorem middleCollapse_unique {L R : SSet.{u}} (m : L ⊗ R ⟶ B)
    (i : B ⟶ P) (k : (L ⊗ X) ⊗ R ⟶ P)
    (sq : IsPushout m (atRight L e ▷ R) i k) (q : P ⟶ X)
    (hi : i ≫ q = toUnit B ≫ e)
    (hk : k ≫ q = fst (L ⊗ X) R ≫ snd L X) : q = middleCollapse e m i k sq :=
  sq.hom_ext (hi.trans (middleCollapse_B e m i k sq).symm)
    (hk.trans (middleCollapse_product e m i k sq).symm)

/-- Strict section equality for that SAME supplied original middle comparison. -/
theorem middle_supplied_section_identity {L R : SSet.{u}}
    (l : 𝟙_ SSet.{u} ⟶ L) (r : 𝟙_ SSet.{u} ⟶ R) (m : L ⊗ R ⟶ B)
    (i : B ⟶ P) (k : (L ⊗ X) ⊗ R ⟶ P)
    (sq : IsPushout m (atRight L e ▷ R) i k) (q : P ⟶ X)
    (hi : i ≫ q = toUnit B ≫ e)
    (hk : k ≫ q = fst (L ⊗ X) R ≫ snd L X) :
    (atLeft (pointPair l r) X ≫ (middleIso L R X).hom ≫ k) ≫ q = 𝟙 X := by
  rw [middleCollapse_unique e m i k sq q hi hk]
  exact section_collapse (pointPair l r) e m i _ (middleIsPushout e m i k sq)

/-- Original W for ANY given comparison with the two full original leg formulas. -/
theorem middle_supplied_geometric {L R : SSet.{u}}
    (l : 𝟙_ SSet.{u} ⟶ L) (r : 𝟙_ SSet.{u} ⟶ R) (m : L ⊗ R ⟶ B)
    (i : B ⟶ P) (k : (L ⊗ X) ⊗ R ⟶ P)
    (sq : IsPushout m (atRight L e ▷ R) i k) (q : P ⟶ X)
    (hi : i ≫ q = toUnit B ≫ e)
    (hk : k ≫ q = fst (L ⊗ X) R ≫ snd L X)
    (hL : SSet.KanComplex.W (TopCat.toSSet.map (SSet.toTop.map (toUnit L))))
    (hR : SSet.KanComplex.W (TopCat.toSSet.map (SSet.toTop.map (toUnit R))))
    (hB : SSet.KanComplex.W (TopCat.toSSet.map (SSet.toTop.map (toUnit B)))) :
    SSet.KanComplex.W (TopCat.toSSet.map (SSet.toTop.map q)) := by
  rw [middleCollapse_unique e m i k sq q hi hk]
  exact middleCollapse_geometric e l r m i k sq hL hR hB

end

end DaggerAmalgamFirstStage
