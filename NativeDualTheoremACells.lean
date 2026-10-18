import NativeStructuredArrowChainDecomposition

/-! The actual dual comma comparison keeps full target chains and full under-chains. -/
set_option autoImplicit false
open CategoryTheory Opposite Simplicial
open DaggerOriginalProductGadget DaggerNativeStructuredArrowChainDecomposition
universe u
namespace DaggerNativeDualTheoremACells
noncomputable section

variable {C D : Type u} [Category.{u} C] [Category.{u} D] (F : C ⥤ D)

def last {q : SimplexCategoryᵒᵖ} (c : (nerve D).obj q) : D :=
  c.obj (Fin.last q.unop.len)

def lastArrow {q r : SimplexCategoryᵒᵖ} (α : q ⟶ r) (c : (nerve D).obj q) :
    last ((nerve D).map α c) ⟶ last c := c.map (homOfLE (Fin.le_last _))

theorem lastArrow_id (q : SimplexCategoryᵒᵖ) (c : (nerve D).obj q) :
    lastArrow (𝟙 q) c = 𝟙 (last c) := c.map_id _

theorem lastArrow_comp {q r s : SimplexCategoryᵒᵖ} (α : q ⟶ r) (β : r ⟶ s)
    (c : (nerve D).obj q) :
    lastArrow (α ≫ β) c = lastArrow β ((nerve D).map α c) ≫ lastArrow α c := by
  change c.map _ = c.map _ ≫ c.map _
  rw [← c.map_comp]
  congr 1

theorem sourceMap_id (d : D) :
    StructuredArrow.map (T := F) (𝟙 d) = 𝟭 (StructuredArrow d F) := by
  have hobj : ∀ P, (StructuredArrow.map (T := F) (𝟙 d)).obj P = P :=
    fun _ ↦ StructuredArrow.map_id
  refine CategoryTheory.Functor.hext hobj ?_
  intro P Q f
  apply hom_heq F (hobj P) (hobj Q)
  rfl

theorem sourceMap_comp {d e f : D} (a : d ⟶ e) (b : e ⟶ f) :
    StructuredArrow.map (T := F) (a ≫ b) =
      StructuredArrow.map b ⋙ StructuredArrow.map a := by
  have hobj : ∀ P, (StructuredArrow.map (T := F) (a ≫ b)).obj P =
      (StructuredArrow.map b ⋙ StructuredArrow.map a).obj P :=
    fun _ ↦ StructuredArrow.map_comp
  refine CategoryTheory.Functor.hext hobj ?_
  intro P Q f
  apply hom_heq F (hobj P) (hobj Q)
  rfl

def rowFamily (q : SimplexCategoryᵒᵖ) (c : (nerve D).obj q) : SSet.{u} :=
  nerve (StructuredArrow (last c) F)

abbrev Cell (q k : SimplexCategoryᵒᵖ) := (familySSet (rowFamily F q)).obj k

def horizontal {q r : SimplexCategoryᵒᵖ} (α : q ⟶ r) (k : SimplexCategoryᵒᵖ)
    (x : Cell F q k) : Cell F r k :=
  ⟨(nerve D).map α x.1, (nerveMap (StructuredArrow.map (T := F)
    (lastArrow α x.1))).app k x.2⟩

theorem horizontal_id (q k : SimplexCategoryᵒᵖ) (x : Cell F q k) :
    horizontal F (𝟙 q) k x = x := by
  rcases x with ⟨c, t⟩
  dsimp only [horizontal]
  rw [lastArrow_id, sourceMap_id F (last c)]
  rfl

theorem horizontal_comp {q r s : SimplexCategoryᵒᵖ} (α : q ⟶ r) (β : r ⟶ s)
    (k : SimplexCategoryᵒᵖ) (x : Cell F q k) :
    horizontal F (α ≫ β) k x = horizontal F β k (horizontal F α k x) := by
  rcases x with ⟨c, t⟩
  dsimp only [horizontal]
  rw [lastArrow_comp, sourceMap_comp]
  rfl

/-- Each row is the actual family of StructuredArrow nerves required by dual Theorem A. -/
def comparison : SimplicialObject SSet.{u} where
  obj q := familySSet (rowFamily F q)
  map {q r} α :=
    { app k := horizontal F α k
      naturality {k l} β := by
        funext x
        dsimp only [horizontal]
        apply congrArg (fun t ↦ (⟨(nerve D).map α x.1, t⟩ : Cell F r l))
        exact congrFun ((nerveMap (StructuredArrow.map (T := F)
          (lastArrow α x.1))).naturality β) x.2 }
  map_id q := by apply NatTrans.ext; funext k x; exact horizontal_id F q k x
  map_comp α β := by apply NatTrans.ext; funext k x; exact horizontal_comp F α β k x

end
end DaggerNativeDualTheoremACells
