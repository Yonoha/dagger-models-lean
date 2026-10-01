import DaggerModels.TwoCopyPushoutReduction
import DaggerModels.TwoObjectCellPushout
import DaggerModels.DaggerSimplicialCofree
import DaggerModels.DaggerSimplicialPresentable

/-! Part I `bg.lem.reduction`: compare the actual dagger cell attachment with the two
ordinary attachments. The reverse ordinary copy has its object labels swapped.
The universal-property comparison below does not assume monicity or distinct endpoints. -/

open CategoryTheory Limits MonoidalCategory

universe u

namespace DaggerModels.TwoObjectCellReduction

noncomputable section

open TwoObjectDaggerGraph (left right)
open TwoObjectCellPushout (apex inl inr spanLeft spanRight)

variable {K L : SSet.{u}}

/-- The actual ordinary one-edge cell map. -/
def ordinaryMap (i : K ⟶ L) := OrdinaryTwoObjectCell.functor.map i

/-- The ordinary forgetful image of the actual free dagger cell map. -/
def daggerMap (i : K ⟶ L) :=
  DaggerSimplicialCat.forget.map (TwoObjectDaggerCell.functor.map i)

@[simp]
theorem spanLeft_naturality (i : K ⟶ L) : spanLeft K ≫ ordinaryMap i = spanLeft L := by
  apply (SimplicialCat.discreteHomEquiv _ _).injective
  funext x
  rcases x with ⟨x⟩
  cases x <;> rfl

@[simp]
theorem spanRight_naturality (i : K ⟶ L) : spanRight K ≫ ordinaryMap i = spanRight L := by
  apply (SimplicialCat.discreteHomEquiv _ _).injective
  funext x
  rcases x with ⟨x⟩
  cases x <;> rfl

/-- The forward ordinary copy commutes with every simplicial cell map. -/
@[reassoc (attr := simp)]
theorem inl_naturality (i : K ⟶ L) : inl K ≫ daggerMap i = ordinaryMap i ≫ inl L := by
  apply (OrdinaryTwoObjectCell.homEquiv K (apex L)).injective
  change (⟨left, right, TwoObjectDaggerCell.generator K ≫ (daggerMap i).map left right⟩ :
    Σ x : (apex L).Obj, Σ y : (apex L).Obj, (K ⟶ (x ⟶[SSet.{u}] y))) =
    ⟨left, right, i ≫ TwoObjectDaggerCell.generator L⟩
  congr 2

/-- The reverse copy also commutes with every simplicial cell map. -/
@[reassoc (attr := simp)]
theorem inr_naturality (i : K ⟶ L) : inr K ≫ daggerMap i = ordinaryMap i ≫ inr L := by
  apply (OrdinaryTwoObjectCell.homEquiv K (apex L)).injective
  change (⟨right, left,
    UnderlyingTwoObjectCell.reverseGenerator K ≫ (daggerMap i).map right left⟩ :
    Σ x : (apex L).Obj, Σ y : (apex L).Obj, (K ⟶ (x ⟶[SSet.{u}] y))) =
    ⟨right, left, i ≫ UnderlyingTwoObjectCell.reverseGenerator L⟩
  congr 2

/-- On generators the reverse copy is exactly the forward generator followed by dagger. -/
theorem generator_dagger (K : SSet.{u}) :
    TwoObjectDaggerCell.generator K ≫ (TwoObjectDaggerCell.cell K).daggerStructure.dagger
      left right =
      UnderlyingTwoObjectCell.reverseGenerator K := by
  simpa only [Category.id_comp] using
    FreeSimplicialPaths.inclusion_dagger (TwoObjectDaggerGraph.graph K) left right

variable {C : DaggerSimplicialCat.{u, u}} (a : TwoObjectDaggerCell.cell K ⟶ C)

/-- Restrict the actual dagger attaching functor to its forward ordinary cell. -/
def forwardAttaching : OrdinaryTwoObjectCell.cell K ⟶ C.toSimplicialCat :=
  inl K ≫ DaggerSimplicialCat.forget.map a

/-- Restrict it to the reverse, swap-labelled ordinary cell. -/
def reverseAttaching : OrdinaryTwoObjectCell.cell K ⟶ C.toSimplicialCat :=
  inr K ≫ DaggerSimplicialCat.forget.map a

theorem forwardAttaching_eq : forwardAttaching a =
    OrdinaryTwoObjectCell.fromData K C.toSimplicialCat (a.obj left) (a.obj right)
      (TwoObjectDaggerCell.generator K ≫ a.map left right) := by
  apply (OrdinaryTwoObjectCell.homEquiv K C.toSimplicialCat).injective
  rfl

/-- The second attaching edge is `u` followed by the target dagger, with reversed endpoints. -/
theorem reverseAttaching_eq : reverseAttaching a =
    OrdinaryTwoObjectCell.fromData K C.toSimplicialCat (a.obj right) (a.obj left)
      (TwoObjectDaggerCell.generator K ≫ a.map left right ≫
        DaggerSimplicialStructure.dagger (a.obj left) (a.obj right)) := by
  apply (OrdinaryTwoObjectCell.homEquiv K C.toSimplicialCat).injective
  change (⟨a.obj right, a.obj left,
    UnderlyingTwoObjectCell.reverseGenerator K ≫ a.map right left⟩ :
      Σ x : C.Obj, Σ y : C.Obj, (K ⟶ (x ⟶[SSet.{u}] y))) = _
  rw [← generator_dagger, Category.assoc, ← a.map_dagger, ← Category.assoc]
  rfl

section Successive

variable (i : K ⟶ L) {Q R : SimplicialCat.{u, u}}
  {b₀ : OrdinaryTwoObjectCell.cell L ⟶ Q} {c₀ : C.toSimplicialCat ⟶ Q}
  {b₁ : OrdinaryTwoObjectCell.cell L ⟶ R} {c₁ : Q ⟶ R}
  (hQ : IsPushout (ordinaryMap i) (forwardAttaching a) b₀ c₀)
  (hR : IsPushout (ordinaryMap i) (reverseAttaching a ≫ c₀) b₁ c₁)

/-- Combine the two new ordinary copies by their actual inner-cell pushout. -/
def combined : apex L ⟶ R :=
  TwoCopyPushoutReduction.combined (TwoObjectCellPushout.isPushout K)
    (TwoObjectCellPushout.isPushout L) (spanLeft_naturality i) (spanRight_naturality i)
    hQ hR

@[reassoc (attr := simp)]
theorem combined_inl : inl L ≫ combined a i hQ hR = b₀ ≫ c₁ :=
  TwoCopyPushoutReduction.combined_inl _ _ _ _ _ _

@[reassoc (attr := simp)]
theorem combined_inr : inr L ≫ combined a i hQ hR = b₁ :=
  TwoCopyPushoutReduction.combined_inr _ _ _ _ _ _

/-- Two successive ordinary attachments satisfy the full forgotten dagger pushout UP. -/
theorem isPushout : IsPushout (daggerMap i) (DaggerSimplicialCat.forget.map a)
    (combined a i hQ hR) (c₀ ≫ c₁) :=
  TwoCopyPushoutReduction.isPushout (TwoObjectCellPushout.isPushout K)
    (TwoObjectCellPushout.isPushout L) (spanLeft_naturality i) (spanRight_naturality i)
    (inl_naturality i) (inr_naturality i) hQ hR

variable {P : DaggerSimplicialCat.{u, u}}
  {b : TwoObjectDaggerCell.cell L ⟶ P} {c : C ⟶ P}
  (hP : IsPushout (TwoObjectDaggerCell.functor.map i) a b c)

include hP in
/-- Colimit preservation comes from the actual cofree adjunction, without ordinary existence. -/
theorem forgotten_isPushout : IsPushout (daggerMap i) (DaggerSimplicialCat.forget.map a)
    (DaggerSimplicialCat.forget.map b) (DaggerSimplicialCat.forget.map c) := by
  letI : PreservesColimitsOfSize.{0, 0} DaggerSimplicialCat.forget.{u, u} :=
    DaggerSimplicialCat.Cofree.forget_preservesColimitsOfSize
  exact hP.map DaggerSimplicialCat.forget

/-- The actual dagger attachment and the two successive ordinary attachments are isomorphic. -/
def comparisonIso : P.toSimplicialCat ≅ R :=
  (forgotten_isPushout a i hP).isoIsPushout _ _ (isPushout a i hQ hR)

@[reassoc (attr := simp)]
theorem comparisonIso_cell : DaggerSimplicialCat.forget.map b ≫
    (comparisonIso a i hQ hR hP).hom = combined a i hQ hR := by
  apply IsPushout.inl_isoIsPushout_hom

@[reassoc (attr := simp)]
theorem comparisonIso_original : DaggerSimplicialCat.forget.map c ≫
    (comparisonIso a i hQ hR hP).hom = c₀ ≫ c₁ := by
  apply IsPushout.inr_isoIsPushout_hom

@[reassoc (attr := simp)]
theorem comparisonIso_forward : (inl L ≫ DaggerSimplicialCat.forget.map b) ≫
    (comparisonIso a i hQ hR hP).hom = b₀ ≫ c₁ := by
  rw [Category.assoc, comparisonIso_cell, combined_inl]

@[reassoc (attr := simp)]
theorem comparisonIso_reverse : (inr L ≫ DaggerSimplicialCat.forget.map b) ≫
    (comparisonIso a i hQ hR hP).hom = b₁ := by
  rw [Category.assoc, comparisonIso_cell, combined_inr]

end Successive

/-- The actual dagger attaching map classified by arbitrary endpoints and an edge map. -/
def attaching (x y : C.Obj) (f : K ⟶ (x ⟶[SSet.{u}] y)) :
    TwoObjectDaggerCell.cell K ⟶ C :=
  (TwoObjectDaggerCell.homEquiv K C).symm ⟨x, y, f⟩

@[simp]
theorem attaching_obj_left (x y : C.Obj) (f : K ⟶ (x ⟶[SSet.{u}] y)) :
    (attaching x y f).obj left = x := rfl

@[simp]
theorem attaching_obj_right (x y : C.Obj) (f : K ⟶ (x ⟶[SSet.{u}] y)) :
    (attaching x y f).obj right = y := rfl

@[simp]
theorem attaching_generator (x y : C.Obj) (f : K ⟶ (x ⟶[SSet.{u}] y)) :
    TwoObjectDaggerCell.generator K ≫ (attaching x y f).map left right = f := by
  have h := (TwoObjectDaggerCell.homEquiv K C).apply_symm_apply ⟨x, y, f⟩
  exact eq_of_heq (congr_arg_heq
    (fun p : Σ a : C.Obj, Σ b : C.Obj, (K ⟶ (a ⟶[SSet.{u}] b)) ↦ p.2.2) h)

/-- The first ordinary attaching map is exactly the displayed `u`. -/
theorem forwardAttaching_data (x y : C.Obj) (f : K ⟶ (x ⟶[SSet.{u}] y)) :
    forwardAttaching (attaching x y f) =
      OrdinaryTwoObjectCell.fromData K C.toSimplicialCat x y f := by
  rw [forwardAttaching_eq, attaching_generator]
  rfl

/-- The second ordinary attaching map is exactly the displayed `u†`, at `(y,x)`. -/
theorem reverseAttaching_data (x y : C.Obj) (f : K ⟶ (x ⟶[SSet.{u}] y)) :
    reverseAttaching (attaching x y f) =
      OrdinaryTwoObjectCell.fromData K C.toSimplicialCat y x
        (f ≫ DaggerSimplicialStructure.dagger x y) := by
  rw [reverseAttaching_eq, ← Category.assoc, attaching_generator]
  rfl

/-- The chosen dagger pushout exists unconditionally from the proved cocompleteness. -/
def daggerAttachment (i : K ⟶ L) (a : TwoObjectDaggerCell.cell K ⟶ C) :
    DaggerSimplicialCat.{u, u} := by
  letI := daggerSimplicialCatHasColimits.{u}
  exact pushout (TwoObjectDaggerCell.functor.map i) a

/-- Its actual new-cell inclusion. -/
def daggerCellInclusion (i : K ⟶ L) (a : TwoObjectDaggerCell.cell K ⟶ C) :
    TwoObjectDaggerCell.cell L ⟶ daggerAttachment i a := by
  letI := daggerSimplicialCatHasColimits.{u}
  exact pushout.inl (TwoObjectDaggerCell.functor.map i) a

/-- Its actual original-category inclusion. -/
def daggerOriginalInclusion (i : K ⟶ L) (a : TwoObjectDaggerCell.cell K ⟶ C) :
    C ⟶ daggerAttachment i a := by
  letI := daggerSimplicialCatHasColimits.{u}
  exact pushout.inr (TwoObjectDaggerCell.functor.map i) a

theorem daggerAttachment_isPushout (i : K ⟶ L) (a : TwoObjectDaggerCell.cell K ⟶ C) :
    IsPushout (TwoObjectDaggerCell.functor.map i) a
      (daggerCellInclusion i a) (daggerOriginalInclusion i a) := by
  letI := daggerSimplicialCatHasColimits.{u}
  exact IsPushout.of_hasPushout _ _

end
end DaggerModels.TwoObjectCellReduction
