import OrdinaryCellComparisonMaps

/-! Comparisons of every original length stage, successor pushout and final cocone. -/
open CategoryTheory MonoidalCategory Limits DaggerModels
open DaggerRelativeOneCellPresentation DaggerOrdinaryWordBoundary
open DaggerOrdinaryReducedWords DaggerOrdinaryCellNormalizer DaggerOrdinaryWordLength
open DaggerOrdinaryWordStages DaggerOrdinaryWordFiltration

universe u
set_option autoImplicit false
namespace DaggerOrdinaryCellComparisonData
noncomputable section

variable {C D E : SimplicialCat.{u, u}} (F : C ⟶ D) (x y : C.Obj) {L : SSet.{u}}
  (A : L.Subcomplex) (uC : (A : SSet.{u}) ⟶ (x ⟶[SSet] y))
  (uD : (A : SSet.{u}) ⟶ (F.obj x ⟶[SSet] F.obj y)) (hu : uC ≫ F.map x y = uD)

theorem QF_id : QF (𝟙 C) x y A uC uC (by simp) = 𝟙 (Q C x y A.ι uC) := by
  apply hom_ext C x y A.ι uC
  · rw [QF_old]
    simp
  · rw [QF_cell]
    simp

theorem QF_comp (G : D ⟶ E)
    (uE : (A : SSet.{u}) ⟶ (G.obj (F.obj x) ⟶[SSet] G.obj (F.obj y)))
    (hG : uD ≫ G.map (F.obj x) (F.obj y) = uE)
    (hFG : uC ≫ (F ≫ G).map x y = uE) :
    QF (F ≫ G) x y A uC uE hFG =
      QF F x y A uC uD hu ≫ QF G (F.obj x) (F.obj y) A uD uE hG := by
  apply hom_ext C x y A.ι uC
  · rw [QF_old, ← Category.assoc, QF_old]
    simp only [Category.assoc]
    rw [QF_old]
    rfl
  · rw [QF_cell, ← Category.assoc, QF_cell, QF_cell]
    rfl

theorem WordF_naturality (n : ℕ) (a b : C.Obj)
    {q q' : SimplexCategoryᵒᵖ} (α : q ⟶ q') (w : (Word C x y L n a b).obj q) :
    (WordF F x y n a b).app q' ((Word C x y L n a b).map α w) =
      (Word D (F.obj x) (F.obj y) L n (F.obj a) (F.obj b)).map α
        ((WordF F x y n a b).app q w) :=
  congrFun ((WordF F x y n a b).naturality α) w

theorem WordF_appendOld (q : SimplexCategoryᵒᵖ) (n : ℕ) (a b c : C.Obj)
    (w : (Word C x y L n a b).obj q) (h : (b ⟶[SSet] c).obj q) :
    (WordF F x y n a c).app q (appendOld C x y L q n a b c w h) =
      appendOld D (F.obj x) (F.obj y) L q n (F.obj a) (F.obj b) (F.obj c)
        ((WordF F x y n a b).app q w) ((F.map b c).app q h) := by
  induction n generalizing a with
  | zero => exact (SimplicialEnrichment.functor F q).map_comp w h
  | succ n ih =>
    change (_, (WordF F x y n y c).app q (appendOld C x y L q n y b c w.2 h)) = _
    rw [ih]
    rfl

theorem WordF_appendNew (q : SimplexCategoryᵒᵖ) (n : ℕ) (a : C.Obj)
    (w : (Word C x y L n a x).obj q) (l : L.obj q) :
    (WordF F x y (n + 1) a y).app q (appendNew C x y L q n a w l) =
      appendNew D (F.obj x) (F.obj y) L q n (F.obj a)
        ((WordF F x y n a x).app q w) l := by
  induction n generalizing a with
  | zero =>
    change (((F.map a x).app q w, l),
      (F.map y y).app q ((eId SSet y).app q PUnit.unit)) =
      (((F.map a x).app q w, l), (eId SSet (F.obj y)).app q PUnit.unit)
    rw [show (F.map y y).app q ((eId SSet y).app q PUnit.unit) =
      (eId SSet (F.obj y)).app q PUnit.unit from
        (SimplicialEnrichment.functor F q).map_id y]
  | succ n ih =>
    change (_, (WordF F x y (n + 1) y y).app q
      (appendNew C x y L q n y w.2 l)) = _
    rw [ih]
    rfl

theorem ReducedF_id (q : SimplexCategoryᵒᵖ) (a b : C.Obj)
    (w : Reduced C x y A q a b) : ReducedF (𝟙 C) x y A q a b w = w := by
  rcases w with ⟨n, w, hw⟩
  apply congrArg (Sigma.mk n)
  apply Subtype.ext
  exact congrFun (NatTrans.congr_app (WordF_id x y n a b) q) w

theorem ReducedF_comp (G : D ⟶ E) (q : SimplexCategoryᵒᵖ) (a b : C.Obj)
    (w : Reduced C x y A q a b) :
    ReducedF (F ≫ G) x y A q a b w =
      ReducedF G (F.obj x) (F.obj y) A q (F.obj a) (F.obj b)
        (ReducedF F x y A q a b w) := by
  rcases w with ⟨n, w, hw⟩
  apply congrArg (Sigma.mk n)
  apply Subtype.ext
  exact congrFun (NatTrans.congr_app (WordF_comp F x y G n a b) q) w

theorem stage_preimage (n : ℕ) (a b : C.Obj) (q : SimplexCategoryᵒᵖ)
    (z : SimplicialCat.HomQuotient.HomObj (relations C x y A.ι uC) q a b) :
    ((QF F x y A uC uD hu).map a b).app q z ∈
        (stage D (F.obj x) (F.obj y) A uD n (F.obj a) (F.obj b)).obj q ↔
      z ∈ (stage C x y A uC n a b).obj q := by
  change (normalize D (F.obj x) (F.obj y) A uD q (F.obj a) (F.obj b)
    (((QF F x y A uC uD hu).map a b).app q z)).1 ≤ n ↔
    (normalize C x y A uC q a b z).1 ≤ n
  rw [normalization_length]

/-- The full original quotient map restricted to its exact same length bound. -/
def StageF (n : ℕ) (a b : C.Obj) :
    (stage C x y A uC n a b : SSet.{u}) ⟶
      (stage D (F.obj x) (F.obj y) A uD n (F.obj a) (F.obj b) : SSet.{u}) where
  app q z := ⟨((QF F x y A uC uD hu).map a b).app q z.val,
    (stage_preimage F x y A uC uD hu n a b q z.val).2 z.property⟩
  naturality {q q'} α := by
    funext z
    apply Subtype.ext
    exact congrFun (((QF F x y A uC uD hu).map a b).naturality α) z.val

theorem StageF_ι (n : ℕ) (a b : C.Obj) :
    StageF F x y A uC uD hu n a b ≫
        (stage D (F.obj x) (F.obj y) A uD n (F.obj a) (F.obj b)).ι =
      (stage C x y A uC n a b).ι ≫ (QF F x y A uC uD hu).map a b := rfl

theorem StageF_zero_hom (a b : C.Obj) :
    (stageZeroIso C x y A uC a b).hom ≫ StageF F x y A uC uD hu 0 a b =
      F.map a b ≫ (stageZeroIso D (F.obj x) (F.obj y) A uD (F.obj a) (F.obj b)).hom := by
  apply (cancel_mono (stage D (F.obj x) (F.obj y) A uD 0 (F.obj a) (F.obj b)).ι).1
  rw [Category.assoc, StageF_ι, ← Category.assoc, stageZeroIso_hom_ι,
    QF_old_map, Category.assoc, stageZeroIso_hom_ι]

theorem StageF_zero_inv (a b : C.Obj) :
    StageF F x y A uC uD hu 0 a b ≫
        (stageZeroIso D (F.obj x) (F.obj y) A uD (F.obj a) (F.obj b)).inv =
      (stageZeroIso C x y A uC a b).inv ≫ F.map a b := by
  apply (cancel_epi (stageZeroIso C x y A uC a b).hom).1
  rw [← Category.assoc, StageF_zero_hom, Category.assoc, Iso.hom_inv_id,
    Category.comp_id, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]

theorem StageF_step (n : ℕ) (a b : C.Obj) :
    step C x y A uC n a b ≫ StageF F x y A uC uD hu (n + 1) a b =
      StageF F x y A uC uD hu n a b ≫
        step D (F.obj x) (F.obj y) A uD n (F.obj a) (F.obj b) := by
  ext q z
  rfl

theorem StageF_word (n : ℕ) (a b : C.Obj) :
    wordToStage C x y A uC n a b ≫ StageF F x y A uC uD hu n a b =
      WordF F x y n a b ≫
        wordToStage D (F.obj x) (F.obj y) A uD n (F.obj a) (F.obj b) := by
  apply (cancel_mono (stage D (F.obj x) (F.obj y) A uD n (F.obj a) (F.obj b)).ι).1
  rw [Category.assoc, StageF_ι, ← Category.assoc, wordToStage_ι,
    evaluation, Category.assoc, wordToStage_ι]

theorem StageF_boundary (n : ℕ) (a b : C.Obj) :
    boundaryToStage C x y A uC n a b ≫ StageF F x y A uC uD hu n a b =
      BoundaryF F x y A (n + 1) a b ≫
        boundaryToStage D (F.obj x) (F.obj y) A uD n (F.obj a) (F.obj b) := by
  ext q w
  exact congrFun (NatTrans.congr_app (evaluation F x y A uC uD hu (n + 1) a b) q) w.val

/-- A genuine transformation of the two original Nat filtrations. -/
def filtrationF (a b : C.Obj) : filtration C x y A uC a b ⟶
    filtration D (F.obj x) (F.obj y) A uD (F.obj a) (F.obj b) where
  app n := StageF F x y A uC uD hu n a b
  naturality n m φ := by ext q z; rfl

theorem filtrationF_cocone (a b : C.Obj) :
    filtrationF F x y A uC uD hu a b ≫
        inclusion D (F.obj x) (F.obj y) A uD (F.obj a) (F.obj b) =
      inclusion C x y A uC a b ≫
        (Functor.const ℕ).map ((QF F x y A uC uD hu).map a b) := rfl

def pulledCocone (a b : C.Obj)
    (s : Cocone (filtration D (F.obj x) (F.obj y) A uD (F.obj a) (F.obj b))) :
    Cocone (filtration C x y A uC a b) :=
  Cocone.mk s.pt (filtrationF F x y A uC uD hu a b ≫ s.ι)

/-- Exact final desc for every actual target cocone, with no chosen-leg shortcut. -/
theorem final_desc (a b : C.Obj)
    (s : Cocone (filtration D (F.obj x) (F.obj y) A uD (F.obj a) (F.obj b))) :
    (QF F x y A uC uD hu).map a b ≫
        filtrationDesc D (F.obj x) (F.obj y) A uD (F.obj a) (F.obj b) s =
      filtrationDesc C x y A uC a b (pulledCocone F x y A uC uD hu a b s) := by
  apply filtrationDesc_unique C x y A uC a b (pulledCocone F x y A uC uD hu a b s)
  intro n
  rw [← Category.assoc, ← StageF_ι, Category.assoc, filtrationDesc_fac]
  rfl

theorem BoundaryF_id (n : ℕ) (a b : C.Obj) :
    BoundaryF (𝟙 C) x y A n a b = 𝟙 _ := by
  ext q w
  exact congrFun (NatTrans.congr_app (WordF_id x y n a b) q) w.val

theorem BoundaryF_comp (G : D ⟶ E) (n : ℕ) (a b : C.Obj) :
    BoundaryF (F ≫ G) x y A n a b = BoundaryF F x y A n a b ≫
      BoundaryF G (F.obj x) (F.obj y) A n (F.obj a) (F.obj b) := by
  ext q w
  exact congrFun (NatTrans.congr_app (WordF_comp F x y G n a b) q) w.val

theorem StageF_id (n : ℕ) (a b : C.Obj) :
    StageF (𝟙 C) x y A uC uC (by simp) n a b = 𝟙 _ := by
  ext q w
  change ((QF (𝟙 C) x y A uC uC (by simp)).map a b).app q w.val = w.val
  have hh : (QF (𝟙 C) x y A uC uC (by simp)).map a b = 𝟙 _ := by
    simpa only [eqToHom_refl, Category.comp_id] using
      enriched_congr_map (QF_id x y A uC) a b
  exact congrFun (NatTrans.congr_app hh q) w.val

theorem StageF_comp (G : D ⟶ E)
    (uE : (A : SSet.{u}) ⟶ (G.obj (F.obj x) ⟶[SSet] G.obj (F.obj y)))
    (hG : uD ≫ G.map (F.obj x) (F.obj y) = uE)
    (hFG : uC ≫ (F ≫ G).map x y = uE) (n : ℕ) (a b : C.Obj) :
    StageF (F ≫ G) x y A uC uE hFG n a b = StageF F x y A uC uD hu n a b ≫
      StageF G (F.obj x) (F.obj y) A uD uE hG n (F.obj a) (F.obj b) := by
  ext q w
  change ((QF (F ≫ G) x y A uC uE hFG).map a b).app q w.val =
    ((QF G (F.obj x) (F.obj y) A uD uE hG).map (F.obj a) (F.obj b)).app q
      (((QF F x y A uC uD hu).map a b).app q w.val)
  have hh := enriched_congr_map (QF_comp F x y A uC uD hu G uE hG hFG) a b
  simpa only [eqToHom_refl, Category.comp_id] using
    congrFun (NatTrans.congr_app hh q) w.val

theorem ReducedF_rightOld (q : SimplexCategoryᵒᵖ) (a b c : C.Obj)
    (w : Reduced C x y A q a b) (h : (b ⟶[SSet] c).obj q) :
    ReducedF F x y A q a c (rightOld C x y A q w h) =
      rightOld D (F.obj x) (F.obj y) A q (ReducedF F x y A q a b w)
        ((F.map b c).app q h) := by
  apply congrArg (Sigma.mk w.1)
  apply Subtype.ext
  exact WordF_appendOld F x y q w.1 a b c w.2.val h

theorem ReducedF_rightNew (q : SimplexCategoryᵒᵖ) (a : C.Obj)
    (w : Reduced C x y A q a x) (l : L.obj q) (hl : l ∉ A.obj q) :
    ReducedF F x y A q a y (rightNew C x y A q w l hl) =
      rightNew D (F.obj x) (F.obj y) A q (ReducedF F x y A q a x w) l hl := by
  apply congrArg (Sigma.mk (w.1 + 1))
  apply Subtype.ext
  exact WordF_appendNew F x y q w.1 a w.2.val l

include hu in
theorem ReducedF_newAction (q : SimplexCategoryᵒᵖ) (a : C.Obj)
    (w : Reduced C x y A q a x) (l : L.obj q) :
    ReducedF F x y A q a y (newAction C x y A uC q w l) =
      newAction D (F.obj x) (F.obj y) A uD q (ReducedF F x y A q a x w) l := by
  classical
  by_cases hl : l ∈ A.obj q
  · simp only [newAction, dif_pos hl]
    rw [ReducedF_rightOld]
    have hh := congrFun (NatTrans.congr_app hu q) ⟨l, hl⟩
    change (F.map x y).app q (uC.app q ⟨l, hl⟩) = uD.app q ⟨l, hl⟩ at hh
    rw [hh]
  · simp only [newAction, dif_neg hl]
    exact ReducedF_rightNew F x y A q a w l hl

theorem QF_nil (q : SimplexCategoryᵒᵖ) (a : C.Obj) :
    ((QF F x y A uC uD hu).map a a).app q
        (SimplicialCat.HomQuotient.mk (relations C x y A.ι uC) q
          (Quiver.Path.nil : Path C x y (L := L) q a a)) =
      SimplicialCat.HomQuotient.mk (relations D (F.obj x) (F.obj y) A.ι uD) q
        (Quiver.Path.nil : Path D (F.obj x) (F.obj y) (L := L) q (F.obj a) (F.obj a)) :=
  (SimplicialEnrichment.functor (QF F x y A uC uD hu) q).map_id a

theorem QF_concat (q : SimplexCategoryᵒᵖ) (a b c : C.Obj)
    (p : Path C x y (L := L) q a b) (s : Path C x y (L := L) q b c) :
    ((QF F x y A uC uD hu).map a c).app q
        (SimplicialCat.HomQuotient.mk (relations C x y A.ι uC) q (p.comp s)) =
      CategoryTheory.Quotient.comp
        (SimplicialCat.HomQuotient.degreeRel
          (relations D (F.obj x) (F.obj y) A.ι uD) q)
        (((QF F x y A uC uD hu).map a b).app q
          (SimplicialCat.HomQuotient.mk (relations C x y A.ι uC) q p))
        (((QF F x y A uC uD hu).map b c).app q
          (SimplicialCat.HomQuotient.mk (relations C x y A.ι uC) q s)) :=
  (SimplicialEnrichment.functor (QF F x y A uC uD hu) q).map_comp
    (SimplicialCat.HomQuotient.mk (relations C x y A.ι uC) q p)
    (SimplicialCat.HomQuotient.mk (relations C x y A.ι uC) q s)

theorem QF_relation (q : SimplexCategoryᵒᵖ) (a b : C.Obj)
    (p p' : Path C x y (L := L) q a b) (h : Rel C x y A.ι uC q a b p p') :
    ((QF F x y A uC uD hu).map a b).app q
        (SimplicialCat.HomQuotient.mk (relations C x y A.ι uC) q p) =
      ((QF F x y A uC uD hu).map a b).app q
        (SimplicialCat.HomQuotient.mk (relations C x y A.ι uC) q p') :=
  congrArg (((QF F x y A uC uD hu).map a b).app q)
    (SimplicialCat.HomQuotient.sound (relations C x y A.ι uC) q h)

end

section SuccessorUP
variable {C D : SimplicialCat.{u, u}} (F : C ⟶ D) (x y : C.Obj) {L : SSet.{u}}
  (A : L.Subcomplex) (uC : (A : SSet.{u}) ⟶ (x ⟶[SSet] y))
  (uD : (A : SSet.{u}) ⟶ (F.obj x ⟶[SSet] F.obj y)) (hu : uC ≫ F.map x y = uD)
  (n : ℕ) (a b : C.Obj) {Z : SSet.{u}}
  (h : (stage D (F.obj x) (F.obj y) A uD n (F.obj a) (F.obj b) : SSet.{u}) ⟶ Z)
  (k : Word D (F.obj x) (F.obj y) L (n + 1) (F.obj a) (F.obj b) ⟶ Z)
  (w : boundaryToStage D (F.obj x) (F.obj y) A uD n (F.obj a) (F.obj b) ≫ h =
    (Boundary D (F.obj x) (F.obj y) A (n + 1) (F.obj a) (F.obj b)).ι ≫ k)

include w in
theorem successor_compatibility :
    boundaryToStage C x y A uC n a b ≫ (StageF F x y A uC uD hu n a b ≫ h) =
      (Boundary C x y A (n + 1) a b).ι ≫ (WordF F x y (n + 1) a b ≫ k) := by
  rw [← Category.assoc, StageF_boundary, Category.assoc, w,
    ← Category.assoc, BoundaryF_ι, Category.assoc]

theorem successor_desc :
    StageF F x y A uC uD hu (n + 1) a b ≫
        (attachment_isPushout D (F.obj x) (F.obj y) A uD n (F.obj a) (F.obj b)).desc h k w =
      (attachment_isPushout C x y A uC n a b).desc
        (StageF F x y A uC uD hu n a b ≫ h) (WordF F x y (n + 1) a b ≫ k)
        (successor_compatibility F x y A uC uD hu n a b h k w) := by
  apply (attachment_isPushout C x y A uC n a b).hom_ext
  · rw [← Category.assoc, StageF_step, Category.assoc, IsPushout.inl_desc,
      IsPushout.inl_desc]
  · rw [← Category.assoc, StageF_word, Category.assoc, IsPushout.inr_desc,
      IsPushout.inr_desc]

end SuccessorUP
end DaggerOrdinaryCellComparisonData
