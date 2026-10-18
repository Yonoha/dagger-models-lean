import OrdinaryFirstWord
import TopCatModelCategory.SSet.AnodyneExtensionsAdjunctions

/-! Actual alternating words with arbitrary original Hom factors. Word length zero is the
original Hom. Positive boundaries contain at least one original attaching letter; this
module does not yet construct deletion maps or identify an enriched pushout. -/

open CategoryTheory MonoidalCategory HomotopicalAlgebra DaggerModels
open scoped SSet.modelCategoryQuillen

universe u

namespace DaggerOrdinaryWordBoundary

noncomputable section

def prefixBoundaryIso (H : SSet.{u}) {L : SSet.{u}} (K : L.Subcomplex) :
    ((⊤ : H.Subcomplex).prod K : SSet.{u}) ≅ H ⊗ (K : SSet.{u}) :=
  SSet.Subcomplex.prodIso _ _ ≪≫ whiskerRightIso (SSet.Subcomplex.topIso H) _

theorem prefixBoundaryIso_inclusion (H : SSet.{u}) {L : SSet.{u}} (K : L.Subcomplex) :
    (prefixBoundaryIso H K).hom ≫ (H ◁ K.ι) = ((⊤ : H.Subcomplex).prod K).ι := by
  ext q w <;> rfl

theorem prefix_boundary_anodyne (H : SSet.{u}) {L : SSet.{u}} (K : L.Subcomplex)
    (hK : SSet.anodyneExtensions K.ι) :
    SSet.anodyneExtensions ((⊤ : H.Subcomplex).prod K).ι := by
  let e : Arrow.mk ((⊤ : H.Subcomplex).prod K).ι ≅ Arrow.mk (H ◁ K.ι) :=
    Arrow.isoMk (prefixBoundaryIso H K) (Iso.refl _) (by
      simpa using (prefixBoundaryIso_inclusion H K).symm)
  exact (SSet.anodyneExtensions.arrow_mk_iso_iff e).2
    (DaggerOrdinaryAnodyneTensor.whiskerLeft K.ι hK H)

variable (C : SimplicialCat.{u, u}) (x y : C.Obj)

/-- Exactly n new letters, separated by original old arrows with their original endpoints. -/
def Word (L : SSet.{u}) : ℕ → C.Obj → C.Obj → SSet.{u}
  | 0, a, b => a ⟶[SSet] b
  | n + 1, a, b => ((a ⟶[SSet] x) ⊗ L) ⊗ Word L n y b

/-- The full attaching boundary; the zero-letter object has empty boundary. -/
def Boundary {L : SSet.{u}} (K : L.Subcomplex) :
    (n : ℕ) → (a b : C.Obj) → (Word C x y L n a b).Subcomplex
  | 0, _, _ => ⊥
  | n + 1, a, b => ((⊤ : (a ⟶[SSet] x).Subcomplex).prod K).unionProd
      (Boundary K n y b)

/-- Each original new letter in a positive word, without forgetting old Hom coordinates. -/
def letter (L : SSet.{u}) : (n : ℕ) → (a b : C.Obj) → (q : SimplexCategoryᵒᵖ) →
    (Word C x y L (n + 1) a b).obj q → Fin (n + 1) → L.obj q
  | 0, _, _, _, w, _ => w.1.2
  | n + 1, _, b, q, w, i => Fin.cases w.1.2 (fun j ↦ letter L n y b q w.2 j) i

theorem letter_map (L : SSet.{u}) (n : ℕ) (a b : C.Obj)
    {q q' : SimplexCategoryᵒᵖ} (α : q ⟶ q')
    (w : (Word C x y L (n + 1) a b).obj q) (i : Fin (n + 1)) :
    letter C x y L n a b q' ((Word C x y L (n + 1) a b).map α w) i =
      L.map α (letter C x y L n a b q w i) := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih =>
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · rfl
    · exact ih y w.2 j

theorem mem_boundary_succ {L : SSet.{u}} (K : L.Subcomplex) (n : ℕ) (a b : C.Obj)
    (q : SimplexCategoryᵒᵖ) (w : (Word C x y L (n + 1) a b).obj q) :
    w ∈ (Boundary C x y K (n + 1) a b).obj q ↔
      w.1.2 ∈ K.obj q ∨ w.2 ∈ (Boundary C x y K n y b).obj q := by
  rw [Boundary, SSet.Subcomplex.mem_unionProd_iff]
  change (True ∧ w.1.2 ∈ K.obj q) ∨ _ ↔ _
  simp only [true_and]

theorem mem_boundary_iff {L : SSet.{u}} (K : L.Subcomplex) (n : ℕ) (a b : C.Obj)
    (q : SimplexCategoryᵒᵖ) (w : (Word C x y L (n + 1) a b).obj q) :
    w ∈ (Boundary C x y K (n + 1) a b).obj q ↔
      ∃ i : Fin (n + 1), letter C x y L n a b q w i ∈ K.obj q := by
  induction n generalizing a with
  | zero =>
    rw [mem_boundary_succ]
    change _ ∨ False ↔ _
    constructor
    · intro h
      exact ⟨0, h.resolve_right id⟩
    · rintro ⟨i, h⟩
      exact Or.inl h
  | succ n ih =>
    rw [mem_boundary_succ, ih y w.2]
    constructor
    · rintro (h | ⟨j, h⟩)
      · exact ⟨0, h⟩
      · exact ⟨j.succ, h⟩
    · rintro ⟨i, h⟩
      cases i using Fin.cases with
      | zero => exact Or.inl h
      | succ j => exact Or.inr ⟨j, h⟩

theorem boundary_inclusion_app {L : SSet.{u}} (K : L.Subcomplex) (n : ℕ)
    (a b : C.Obj) (q : SimplexCategoryᵒᵖ)
    (w : (Boundary C x y K n a b : SSet.{u}).obj q) :
    (Boundary C x y K n a b).ι.app q w = w.val := rfl

theorem boundary_inclusion_mono {L : SSet.{u}} (K : L.Subcomplex) (n : ℕ) (a b : C.Obj) :
    Mono (Boundary C x y K n a b).ι := inferInstance

theorem boundary_anodyne {L : SSet.{u}} (K : L.Subcomplex)
    (hK : SSet.anodyneExtensions K.ι) (n : ℕ) (a b : C.Obj) :
    SSet.anodyneExtensions (Boundary C x y K (n + 1) a b).ι :=
  SSet.anodyneExtensions.subcomplex_unionProd_mem_of_left _ _
    (prefix_boundary_anodyne (a ⟶[SSet] x) K hK)

theorem boundary_trivialCofibration {L : SSet.{u}} (K : L.Subcomplex)
    (hK : SSet.anodyneExtensions K.ι) (n : ℕ) (a b : C.Obj) :
    trivialCofibrations SSet.{u} (Boundary C x y K (n + 1) a b).ι :=
  (DaggerOrdinaryAnodyneTensor.anodyne_iff_trivialCofibration _).1
    (boundary_anodyne C x y K hK n a b)

theorem horn_boundary (d : ℕ) (k : Fin (d + 2)) (n : ℕ) (a b : C.Obj) :
    trivialCofibrations SSet.{u}
      (Boundary C x y (SSet.horn.{u} (d + 1) k) (n + 1) a b).ι :=
  boundary_trivialCofibration C x y _ (SSet.anodyneExtensions.horn_ι_mem d k) n a b

theorem word_zero (L : SSet.{u}) (a b : C.Obj) : Word C x y L 0 a b = (a ⟶[SSet] b) := rfl

theorem word_one (L : SSet.{u}) (a b : C.Obj) :
    Word C x y L 1 a b = DaggerOrdinaryFirstWord.WordObject (L := L) x y a b := rfl

theorem mem_boundary_one {L : SSet.{u}} (K : L.Subcomplex) (a b : C.Obj)
    (q : SimplexCategoryᵒᵖ) (w : (Word C x y L 1 a b).obj q) :
    w ∈ (Boundary C x y K 1 a b).obj q ↔ w.1.2 ∈ K.obj q := by
  rw [mem_boundary_succ]
  change _ ∨ False ↔ _
  simp only [or_false]

/-- The full first boundary is the original first-stage tensor object, with all old arrows. -/
def oneBoundaryIso {L : SSet.{u}} (K : L.Subcomplex) (a b : C.Obj) :
    (Boundary C x y K 1 a b : SSet.{u}) ≅
      DaggerOrdinaryFirstWord.WordBoundary (K := (K : SSet.{u})) x y a b where
  hom :=
    { app := fun q w ↦
        ((w.val.1.1, ⟨w.val.1.2, (mem_boundary_one C x y K a b q w.val).1 w.property⟩),
          w.val.2)
      naturality := by intros; rfl }
  inv :=
    { app := fun q w ↦
        ⟨((w.1.1, w.1.2.val), w.2),
          (mem_boundary_one C x y K a b q _).2 w.1.2.property⟩
      naturality := by intros; rfl }
  hom_inv_id := by ext q w; rfl
  inv_hom_id := by ext q w <;> rfl

theorem oneBoundaryIso_inclusion {L : SSet.{u}} (K : L.Subcomplex) (a b : C.Obj) :
    (oneBoundaryIso C x y K a b).hom ≫ DaggerOrdinaryFirstWord.wordMap K.ι x y a b =
      (Boundary C x y K 1 a b).ι := by
  ext q w <;> rfl

/-- The actual first boundary arrow agrees with the already constructed first-stage map. -/
def oneBoundaryArrowIso {L : SSet.{u}} (K : L.Subcomplex) (a b : C.Obj) :
    Arrow.mk (Boundary C x y K 1 a b).ι ≅
      Arrow.mk (DaggerOrdinaryFirstWord.wordMap K.ι x y a b) :=
  Arrow.isoMk (oneBoundaryIso C x y K a b) (Iso.refl _) (by
    simpa using (oneBoundaryIso_inclusion C x y K a b).symm)

end

end DaggerOrdinaryWordBoundary
