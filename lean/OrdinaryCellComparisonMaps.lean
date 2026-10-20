import OrdinaryWordFiltration
import OrdinaryWordStages
import OrdinaryCellComparison

/-! Full functorial comparison of the original relative presentations and word tuples.
Old identities remain coordinates; every original new L letter is unchanged. -/

open CategoryTheory MonoidalCategory Limits DaggerModels
open DaggerRelativeOneCellPresentation DaggerOrdinaryWordBoundary
open DaggerOrdinaryReducedWords DaggerOrdinaryCellNormalizer DaggerOrdinaryWordLength

universe u
set_option autoImplicit false
namespace DaggerOrdinaryCellComparisonData
noncomputable section

variable {C D E : SimplicialCat.{u, u}} (F : C ⟶ D) (x y : C.Obj) {L : SSet.{u}}

/-- Exactly the accepted original word, with unchanged new-letter coordinates. -/
def WordF : (n : ℕ) → (a b : C.Obj) →
    Word C x y L n a b ⟶ Word D (F.obj x) (F.obj y) L n (F.obj a) (F.obj b)
  | 0, a, b => F.map a b
  | n + 1, a, b => (F.map a x ⊗ₘ 𝟙 L) ⊗ₘ WordF n y b

theorem WordF_zero (a b : C.Obj) : WordF F x y (L := L) 0 a b = F.map a b := rfl

theorem WordF_succ (n : ℕ) (a b : C.Obj) :
    WordF F x y (L := L) (n + 1) a b =
      (F.map a x ⊗ₘ 𝟙 L) ⊗ₘ WordF F x y n y b := rfl

theorem WordF_id (n : ℕ) (a b : C.Obj) :
    WordF (𝟙 C) x y (L := L) n a b = 𝟙 _ := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih =>
    ext q w
    change (((((𝟙 C : C ⟶ C).map a x).app q w.1.1, w.1.2),
      (WordF (𝟙 C) x y (L := L) n y b).app q w.2)) = w
    rw [ih]
    rfl

theorem WordF_comp (G : D ⟶ E) (n : ℕ) (a b : C.Obj) :
    WordF (F ≫ G) x y (L := L) n a b =
      WordF F x y n a b ≫ WordF G (F.obj x) (F.obj y) n (F.obj a) (F.obj b) := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih =>
    ext q w
    change ((((F ≫ G).map a x).app q w.1.1, w.1.2),
      (WordF (F ≫ G) x y (L := L) n y b).app q w.2) = _
    rw [ih]
    rfl

theorem WordF_letter (n : ℕ) (a b : C.Obj) (q : SimplexCategoryᵒᵖ)
    (w : (Word C x y L (n + 1) a b).obj q) (i : Fin (n + 1)) :
    letter D (F.obj x) (F.obj y) L n (F.obj a) (F.obj b) q
      ((WordF F x y (n + 1) a b).app q w) i = letter C x y L n a b q w i := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih =>
    refine Fin.cases rfl (fun j ↦ ?_) i
    exact ih y w.2 j

theorem Boundary_preimage (A : L.Subcomplex) (n : ℕ) (a b : C.Obj)
    (q : SimplexCategoryᵒᵖ) (w : (Word C x y L n a b).obj q) :
    (WordF F x y n a b).app q w ∈
        (Boundary D (F.obj x) (F.obj y) A n (F.obj a) (F.obj b)).obj q ↔
      w ∈ (Boundary C x y A n a b).obj q := by
  cases n with
  | zero => rfl
  | succ n =>
    simp only [mem_boundary_iff, WordF_letter]

def BoundaryF (A : L.Subcomplex) (n : ℕ) (a b : C.Obj) :
    (Boundary C x y A n a b : SSet.{u}) ⟶
      (Boundary D (F.obj x) (F.obj y) A n (F.obj a) (F.obj b) : SSet.{u}) where
  app q w := ⟨(WordF F x y n a b).app q w.val,
    (Boundary_preimage F x y A n a b q w.val).2 w.property⟩
  naturality {q q'} α := by
    funext w
    apply Subtype.ext
    exact congrFun ((WordF F x y n a b).naturality α) w.val

theorem BoundaryF_ι (A : L.Subcomplex) (n : ℕ) (a b : C.Obj) :
    BoundaryF F x y A n a b ≫ (Boundary D (F.obj x) (F.obj y) A n
      (F.obj a) (F.obj b)).ι = (Boundary C x y A n a b).ι ≫ WordF F x y n a b := rfl

def ReducedF (A : L.Subcomplex) (q : SimplexCategoryᵒᵖ) (a b : C.Obj)
    (w : Reduced C x y A q a b) : Reduced D (F.obj x) (F.obj y) A q (F.obj a) (F.obj b) :=
  ⟨w.1, (WordF F x y w.1 a b).app q w.2.val,
    fun h ↦ w.2.property ((Boundary_preimage F x y A w.1 a b q w.2.val).1 h)⟩

theorem ReducedF_length (A : L.Subcomplex) (q : SimplexCategoryᵒᵖ) (a b : C.Obj)
    (w : Reduced C x y A q a b) : (ReducedF F x y A q a b w).1 = w.1 := rfl

variable (A : L.Subcomplex) (uC : (A : SSet.{u}) ⟶ (x ⟶[SSet] y))
  (uD : (A : SSet.{u}) ⟶ (F.obj x ⟶[SSet] F.obj y)) (hu : uC ≫ F.map x y = uD)

/-- Original desc, without replacing the actual quotient or its object type. -/
def QF : Q C x y A.ι uC ⟶ Q D (F.obj x) (F.obj y) A.ι uD :=
  desc C x y A.ι uC (F ≫ v D (F.obj x) (F.obj y) A.ι uD)
    (newMap D (F.obj x) (F.obj y) A.ι uD) (by
      rw [attaching_equation]
      change uD ≫ (v D (F.obj x) (F.obj y) A.ι uD).map _ _ =
        uC ≫ (F.map x y ≫ (v D (F.obj x) (F.obj y) A.ι uD).map _ _)
      rw [← Category.assoc, hu])

theorem QF_obj (a : C.Obj) : (QF F x y A uC uD hu).obj a = F.obj a := rfl

theorem QF_old : v C x y A.ι uC ≫ QF F x y A uC uD hu =
    F ≫ v D (F.obj x) (F.obj y) A.ι uD := v_desc ..

theorem QF_new : newMap C x y A.ι uC ≫ (QF F x y A uC uD hu).map x y =
    newMap D (F.obj x) (F.obj y) A.ι uD := newMap_desc ..

theorem QF_cell : t C x y A.ι uC ≫ QF F x y A uC uD hu =
    t D (F.obj x) (F.obj y) A.ι uD := t_desc ..

theorem QF_old_map (a b : C.Obj) :
    (v C x y A.ι uC).map a b ≫ (QF F x y A uC uD hu).map a b =
      F.map a b ≫ (v D (F.obj x) (F.obj y) A.ι uD).map (F.obj a) (F.obj b) := by
  simpa only [SimplicialCat.comp_map, eqToHom_refl, Category.comp_id] using
    enriched_congr_map (QF_old F x y A uC uD hu) a b

theorem QF_old_app (q : SimplexCategoryᵒᵖ) (a b : C.Obj) (h : (a ⟶[SSet] b).obj q) :
    ((QF F x y A uC uD hu).map a b).app q
        (SimplicialCat.HomQuotient.mk (relations C x y A.ι uC) q (oldPath C x y q h)) =
      SimplicialCat.HomQuotient.mk (relations D (F.obj x) (F.obj y) A.ι uD) q
        (oldPath D (F.obj x) (F.obj y) q ((F.map a b).app q h)) :=
  congrFun (NatTrans.congr_app (QF_old_map F x y A uC uD hu a b) q) h

theorem QF_new_app (q : SimplexCategoryᵒᵖ) (l : L.obj q) :
    ((QF F x y A uC uD hu).map x y).app q
        (SimplicialCat.HomQuotient.mk (relations C x y A.ι uC) q (newPath C x y q l)) =
      SimplicialCat.HomQuotient.mk (relations D (F.obj x) (F.obj y) A.ι uD) q
        (newPath D (F.obj x) (F.obj y) q l) :=
  congrFun (NatTrans.congr_app (QF_new F x y A uC uD hu) q) l

theorem evaluation (n : ℕ) (a b : C.Obj) :
    wordEvaluation C x y A uC n a b ≫ (QF F x y A uC uD hu).map a b =
      WordF F x y n a b ≫
        wordEvaluation D (F.obj x) (F.obj y) A uD n (F.obj a) (F.obj b) := by
  ext q w
  induction n generalizing a with
  | zero => exact QF_old_app F x y A uC uD hu q a b w
  | succ n ih =>
    change (SimplicialEnrichment.functor (QF F x y A uC uD hu) q).map
      ((SimplicialCat.HomQuotient.mk (relations C x y A.ι uC) q
        (oldPath C x y q w.1.1)) ≫
        ((SimplicialCat.HomQuotient.mk (relations C x y A.ι uC) q
          (newPath C x y q w.1.2)) ≫
          (wordEvaluation C x y A uC n y b).app q w.2)) = _
    rw [Functor.map_comp, Functor.map_comp]
    dsimp only [SimplicialEnrichment.functor]
    rw [QF_old_app, QF_new_app]
    have ht := ih y w.2
    change ((QF F x y A uC uD hu).map y b).app q
        ((wordEvaluation C x y A uC n y b).app q w.2) =
      (wordEvaluation D (F.obj x) (F.obj y) A uD n (F.obj y) (F.obj b)).app q
        ((WordF F x y n y b).app q w.2) at ht
    rw [ht]
    rfl

theorem decodeClass_ReducedF (q : SimplexCategoryᵒᵖ) (a b : C.Obj)
    (w : Reduced C x y A q a b) :
    decodeClass D (F.obj x) (F.obj y) A uD q (ReducedF F x y A q a b w) =
      ((QF F x y A uC uD hu).map a b).app q (decodeClass C x y A uC q w) :=
  (congrFun (NatTrans.congr_app (evaluation F x y A uC uD hu w.1 a b) q) w.2.val).symm

theorem normalization (q : SimplexCategoryᵒᵖ) (a b : C.Obj)
    (z : SimplicialCat.HomQuotient.HomObj (relations C x y A.ι uC) q a b) :
    normalize D (F.obj x) (F.obj y) A uD q (F.obj a) (F.obj b)
        (((QF F x y A uC uD hu).map a b).app q z) =
      ReducedF F x y A q a b (normalize C x y A uC q a b z) := by
  apply (homEquiv D (F.obj x) (F.obj y) A uD q (F.obj a) (F.obj b)).symm.injective
  change decodeClass D (F.obj x) (F.obj y) A uD q
      (normalize D (F.obj x) (F.obj y) A uD q (F.obj a) (F.obj b) _) =
    decodeClass D (F.obj x) (F.obj y) A uD q
      (ReducedF F x y A q a b (normalize C x y A uC q a b z))
  rw [decodeClass_normalize, decodeClass_ReducedF, decodeClass_normalize]

theorem normalization_length (q : SimplexCategoryᵒᵖ) (a b : C.Obj)
    (z : SimplicialCat.HomQuotient.HomObj (relations C x y A.ι uC) q a b) :
    (normalize D (F.obj x) (F.obj y) A uD q (F.obj a) (F.obj b)
      (((QF F x y A uC uD hu).map a b).app q z)).1 =
        (normalize C x y A uC q a b z).1 := by
  rw [normalization]
  rfl

end
end DaggerOrdinaryCellComparisonData
