import RigidificationCofExtremeBoundary
import RigidificationCofBase
import NerveHomotopy
import IinjBridge
import TopCatModelCategory.ModelCategorySSet

set_option autoImplicit false

open CategoryTheory CategoryTheory.Category Simplicial Opposite HomotopicalAlgebra
open MonoidalCategory
open scoped SSet.modelCategoryQuillen

universe u

namespace DaggerOrdinaryRigidificationCof.PathFacets

noncomputable section

variable (n : ℕ) (k : interior n)

/-- The full facet union supplied by the inner horn missing the `k`-th face. -/
def extremeHorn : (extremeHom.{u} n).Subcomplex :=
  (⨆ l : interior n, extremeCut n l) ⊔
    (⨆ l : {l : interior n // l ≠ k}, extremeOmitted n l.1)

theorem cut_le_extremeHorn (l : interior n) :
    extremeCut.{u} n l ≤ extremeHorn n k :=
  (le_iSup (fun j : interior n ↦ extremeCut n j) l).trans le_sup_left

theorem omitted_le_extremeHorn (l : interior n) (hl : l ≠ k) :
    extremeOmitted.{u} n l ≤ extremeHorn n k :=
  (le_iSup (fun j : {j : interior n // j ≠ k} ↦ extremeOmitted n j.1)
    ⟨l, hl⟩).trans le_sup_right

theorem mem_extremeHorn (q : SimplexCategoryᵒᵖ)
    (γ : (extremeHom.{u} n).obj q) :
    γ ∈ (extremeHorn n k).obj q ↔
      (∃ l : interior n, ∀ t, ULift.up l.val ∈ (γ.obj t).I) ∨
      (∃ l : interior n, l ≠ k ∧ ∀ t, ULift.up l.val ∉ (γ.obj t).I) := by
  change (γ ∈ (⨆ l : interior n, extremeCut n l).obj q ∨
    γ ∈ (⨆ l : {l : interior n // l ≠ k}, extremeOmitted n l.1).obj q) ↔ _
  simp only [Subfunctor.iSup_obj, Set.mem_iUnion]
  constructor
  · rintro (⟨l, h⟩ | ⟨⟨l, hl⟩, h⟩)
    · exact Or.inl ⟨l, h⟩
    · exact Or.inr ⟨l, hl, h⟩
  · rintro (⟨l, h⟩ | ⟨l, hl, h⟩)
    · exact Or.inl ⟨l, h⟩
    · exact Or.inr ⟨⟨l, hl⟩, h⟩

private abbrev P : Type u :=
  SimplicialThickening.Path (ULift.up (0 : Fin (n + 2)))
    (ULift.up (Fin.last (n + 1)))

/-- Insert the missing interior vertex into the original Mathlib Path. -/
private def insertPath (p : P n) : P n where
  I := p.I ∪ {ULift.up k.val}
  left := Or.inl p.left
  right := Or.inl p.right
  left_le x hx := by
    rcases hx with hx | hx
    · exact p.left_le x hx
    · subst x
      change (0 : Fin (n + 2)) ≤ k.val
      exact Fin.zero_le _
  le_right x hx := by
    rcases hx with hx | hx
    · exact p.le_right x hx
    · subst x
      change k.val ≤ Fin.last (n + 1)
      exact Fin.le_last _

private def insertFunctor : P n ⥤ P n where
  obj := insertPath n k
  map f := ⟨⟨⟨Set.union_subset_union f.1.1.1 (fun _ h ↦ h)⟩⟩⟩
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

private def insertNat : 𝟭 (P n) ⟶ insertFunctor n k where
  app _ := ⟨⟨⟨fun _ h ↦ Or.inl h⟩⟩⟩
  naturality _ _ _ := Subsingleton.elim _ _

private theorem insertPath_mem (p : P n) :
    ULift.up k.val ∈ (insertPath n k p).I := Or.inr rfl

private theorem insertPath_preserves_mem (p : P n) (l : interior n)
    (hl : ULift.up l.val ∈ p.I) :
    ULift.up l.val ∈ (insertPath n k p).I := Or.inl hl

private theorem insertPath_preserves_omission (p : P n) (l : interior n)
    (hl : l ≠ k) (ho : ULift.up l.val ∉ p.I) :
    ULift.up l.val ∉ (insertPath n k p).I := by
  rintro (h | h)
  · exact ho h
  · exact hl (Subtype.ext (ULift.up_injective h))

/-- The insertion map lands in the `k`-cut, hence in the literal inner cube horn. -/
def insertionRetraction : extremeHom.{u} n ⟶ extremeHorn n k where
  app q γ := ⟨(nerveMap (insertFunctor n k)).app q γ, by
    apply (cut_le_extremeHorn n k k) q
    intro t
    change ULift.up k.val ∈ (insertPath n k (γ.obj t)).I
    exact insertPath_mem n k _⟩
  naturality _ _ _ := rfl

@[reassoc (attr := simp)]
theorem insertionRetraction_ι :
    insertionRetraction.{u} n k ≫ (extremeHorn n k).ι =
      nerveMap (insertFunctor n k) := rfl

/-- Each mixed prism vertex is either the original path or its `k`-insertion. -/
private theorem mixedPath (q : SimplexCategoryᵒᵖ)
    (γ : (extremeHom.{u} n).obj q) (s : (SSet.stdSimplex.obj ⦋1⦌).obj q)
    (t : Fin (q.unop.len + 1)) :
    ((DaggerNerveHomotopy.natTransMap (insertNat n k)).app q (γ, s)).obj t =
      γ.obj t ∨
    ((DaggerNerveHomotopy.natTransMap (insertNat n k)).app q (γ, s)).obj t =
      insertPath n k (γ.obj t) := by
  let i : Fin 2 := (SSet.stdSimplex.objEquiv s).toOrderHom t
  have hi : i = 0 ∨ i = 1 := by
    have h : ∀ j : Fin 2, j = 0 ∨ j = 1 := by decide
    exact h i
  rcases hi with hi | hi
  · left
    change ((ComposableArrows.mk₁ (insertNat n k)).obj i).obj (γ.obj t) = _
    simp [hi]
  · right
    change ((ComposableArrows.mk₁ (insertNat n k)).obj i).obj (γ.obj t) = _
    simp [hi, insertFunctor]

/-- The original nerve prism restricts to the facet union, not merely its endpoints. -/
def extremeHornPrism :
    (extremeHorn.{u} n k : SSet) ⊗ SSet.stdSimplex.obj ⦋1⦌ ⟶
      (extremeHorn n k : SSet) where
  app q z := ⟨(DaggerNerveHomotopy.natTransMap (insertNat n k)).app q
      (z.1.val, z.2), by
    have hz := (mem_extremeHorn n k q z.1.val).mp z.1.property
    apply (mem_extremeHorn n k q _).mpr
    rcases hz with ⟨l, hl⟩ | ⟨l, hlk, hl⟩
    · left
      refine ⟨l, fun t ↦ ?_⟩
      rcases mixedPath n k q z.1.val z.2 t with h | h
      · rw [h]
        exact hl t
      · rw [h]
        exact insertPath_preserves_mem n k _ l (hl t)
    · right
      refine ⟨l, hlk, fun t ↦ ?_⟩
      rcases mixedPath n k q z.1.val z.2 t with h | h
      · rw [h]
        exact hl t
      · rw [h]
        exact insertPath_preserves_omission n k _ l hlk (hl t)⟩
  naturality _ _ _ := by funext z; apply Subtype.ext; rfl

@[reassoc (attr := simp)]
theorem extremeHornPrism_ι :
    extremeHornPrism.{u} n k ≫ (extremeHorn n k).ι =
      ((extremeHorn n k).ι ▷ SSet.stdSimplex.obj ⦋1⦌) ≫
        DaggerNerveHomotopy.natTransMap (insertNat n k) := rfl

private theorem extremeHornPrism_zero :
    SSet.ι₀ ≫ extremeHornPrism.{u} n k = 𝟙 _ := by
  apply (cancel_mono (extremeHorn.{u} n k).ι).mp
  rw [Category.assoc, extremeHornPrism_ι]
  simp [DaggerNerveHomotopy.natTransMap_zero]
  rfl

private theorem extremeHornPrism_one :
    SSet.ι₁ ≫ extremeHornPrism.{u} n k =
      (extremeHorn n k).ι ≫ insertionRetraction n k := by
  apply (cancel_mono (extremeHorn.{u} n k).ι).mp
  rw [Category.assoc, extremeHornPrism_ι, Category.assoc, insertionRetraction_ι]
  simp [DaggerNerveHomotopy.natTransMap_one]

/-- The horn-side actual simplicial homotopy, with its full prism map. -/
def extremeHornHomotopy :
    SSet.Homotopy (𝟙 (extremeHorn.{u} n k : SSet))
      ((extremeHorn n k).ι ≫ insertionRetraction n k) :=
  SSet.Homotopy.mk (extremeHornPrism n k)
    (extremeHornPrism_zero n k) (extremeHornPrism_one n k)

/-- The same insertion homotopy on the entire original Path nerve. -/
def extremeHomHomotopy :
    SSet.Homotopy (𝟙 (extremeHom.{u} n))
      (insertionRetraction n k ≫ (extremeHorn n k).ι) :=
  (DaggerNerveHomotopy.natTransHomotopy (insertNat n k)).congr
    (by rfl) (insertionRetraction_ι n k).symm

/-- The literal cube-horn inclusion becomes a homotopy equivalence under `R`. -/
def extremeHornHomotopyEquivR :
    SSet.HomotopyEquiv
      (DaggerNerveHomotopy.R.obj (extremeHorn.{u} n k : SSet))
      (DaggerNerveHomotopy.R.obj (extremeHom n)) where
  hom := DaggerNerveHomotopy.R.map (extremeHorn n k).ι
  inv := DaggerNerveHomotopy.R.map (insertionRetraction n k)
  homInvId := by
    have h := (extremeHornHomotopy n k).toTop.toSSet
    exact SSet.Homotopy.congr h.symm (by simp [← Functor.map_comp]) (by simp)
  invHomId := by
    have h := (extremeHomHomotopy n k).toTop.toSSet
    exact SSet.Homotopy.congr h.symm (by simp [← Functor.map_comp]) (by simp)

/-- The actual missing-face inclusion is a geometric Kan weak equivalence. -/
theorem extremeHorn_geometric :
    geometric (extremeHorn.{u} n k).ι :=
  SSet.KanComplex.W.homotopyEquivHom (extremeHornHomotopyEquivR n k)

/-- The scalar missing-cube-face inclusion lifts against every Kan fibration. -/
theorem extremeHorn_lifting {X Y : SSet.{u}} (p : X ⟶ Y)
    (hp : Fibration p) :
    HasLiftingProperty (extremeHorn n k).ι p := by
  letI : WeakEquivalence (extremeHorn.{u} n k).ι :=
    (DaggerModels.KanQuillenReuse.weakEquivalence_iff_geometric _).2
      (extremeHorn_geometric n k)
  letI : Cofibration (extremeHorn.{u} n k).ι :=
    SSet.modelCategoryQuillen.cofibration_of_mono _
  letI : Fibration p := hp
  infer_instance

end

end DaggerOrdinaryRigidificationCof.PathFacets
