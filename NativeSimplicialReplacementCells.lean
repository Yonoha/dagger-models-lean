import ProofActualSecondConeProjection

/-! Literal cells of the simplicial replacement of an actual simplicial-set diagram. -/
set_option autoImplicit false
open CategoryTheory Opposite
universe u
namespace DaggerNativeSimplicialReplacementCells
noncomputable section

variable {C : Type u} [Category.{u} C] (G : C ⥤ SSet.{u})

abbrev Chain (q : SimplexCategoryᵒᵖ) := (nerve C).obj q

def first {q : SimplexCategoryᵒᵖ} (c : Chain (C := C) q) : C := c.obj 0

def initialArrow {q r : SimplexCategoryᵒᵖ} (α : q ⟶ r) (c : Chain (C := C) q) :
    first c ⟶ first ((nerve C).map α c) := c.map (homOfLE (Fin.zero_le _))

theorem initialArrow_id (q : SimplexCategoryᵒᵖ) (c : Chain (C := C) q) :
    initialArrow (𝟙 q) c = 𝟙 (first c) := c.map_id 0

theorem initialArrow_comp {q r s : SimplexCategoryᵒᵖ} (α : q ⟶ r) (β : r ⟶ s)
    (c : Chain (C := C) q) :
    initialArrow (α ≫ β) c = initialArrow α c ≫ initialArrow β ((nerve C).map α c) := by
  change c.map _ = c.map _ ≫ c.map _
  rw [← c.map_comp]
  congr 1

def family (q : SimplexCategoryᵒᵖ) (c : Chain (C := C) q) : SSet.{u} := G.obj (first c)

abbrev Cell (q k : SimplexCategoryᵒᵖ) :=
  (DaggerOriginalProductGadget.familySSet (family G q)).obj k

def horizontal {q r : SimplexCategoryᵒᵖ} (α : q ⟶ r) (k : SimplexCategoryᵒᵖ)
    (x : Cell G q k) : Cell G r k :=
  ⟨(nerve C).map α x.1, (G.map (initialArrow α x.1)).app k x.2⟩

def vertical (q : SimplexCategoryᵒᵖ) {k l : SimplexCategoryᵒᵖ} (β : k ⟶ l)
    (x : Cell G q k) : Cell G q l := ⟨x.1, (G.obj (first x.1)).map β x.2⟩

theorem horizontal_id (q k : SimplexCategoryᵒᵖ) (x : Cell G q k) :
    horizontal G (𝟙 q) k x = x := by
  rcases x with ⟨c, t⟩
  dsimp only [horizontal]
  rw [initialArrow_id, G.map_id]
  rfl

theorem horizontal_comp {q r s : SimplexCategoryᵒᵖ} (α : q ⟶ r) (β : r ⟶ s)
    (k : SimplexCategoryᵒᵖ) (x : Cell G q k) :
    horizontal G (α ≫ β) k x = horizontal G β k (horizontal G α k x) := by
  rcases x with ⟨c, t⟩
  dsimp only [horizontal]
  rw [initialArrow_comp, G.map_comp]
  rfl

theorem vertical_id (q k : SimplexCategoryᵒᵖ) (x : Cell G q k) :
    vertical G q (𝟙 k) x = x := by
  rcases x with ⟨c, t⟩
  dsimp only [vertical]
  rw [(G.obj (first c)).map_id]
  rfl

theorem vertical_comp (q : SimplexCategoryᵒᵖ) {k l m : SimplexCategoryᵒᵖ}
    (β : k ⟶ l) (γ : l ⟶ m) (x : Cell G q k) :
    vertical G q (β ≫ γ) x = vertical G q γ (vertical G q β x) := by
  rcases x with ⟨c, t⟩
  dsimp only [vertical]
  rw [(G.obj (first c)).map_comp]
  rfl

/-- All horizontal and vertical operators commute on each entire parameter simplex. -/
theorem operators_commute {q r k l : SimplexCategoryᵒᵖ} (α : q ⟶ r) (β : k ⟶ l)
    (x : Cell G q k) :
    horizontal G α l (vertical G q β x) = vertical G r β (horizontal G α k x) := by
  rcases x with ⟨c, t⟩
  dsimp only [horizontal, vertical]
  apply congrArg (fun t ↦ (⟨(nerve C).map α c, t⟩ : Cell G r l))
  exact congrFun ((G.map (initialArrow α c)).naturality β) t

end
end DaggerNativeSimplicialReplacementCells
