import OrdinaryPiZeroCategory
import TopCatModelCategory.SSet.Monoidal

set_option autoImplicit false
set_option maxHeartbeats 0
open CategoryTheory MonoidalCategory CartesianMonoidalCategory Opposite Simplicial DaggerModels

universe o o₂ v

namespace DaggerOrdinaryPiZeroCategory

def classOfVertex (C : SimplicialCat.{o, v}) {x y : hC C}
    (a : (C.enriched.Hom x y) _⦋0⦌) : x ⟶ y := SSet.π₀.mk a

end DaggerOrdinaryPiZeroCategory

namespace DaggerOrdinaryTranslation

noncomputable section
variable (C : SimplicialCat.{o, v})

abbrev H (x y : C.Obj) : SSet.{v} := C.enriched.Hom x y

def idVertex (x : C.Obj) : H C x x _⦋0⦌ := (C.enriched.id x).app _ PUnit.unit

def compVertex {x y z : C.Obj} (a : H C x y _⦋0⦌) (b : H C y z _⦋0⦌) :
    H C x z _⦋0⦌ := (C.enriched.comp x y z).app _ (a, b)

def vertexAt {x y : C.Obj} (a : H C x y _⦋0⦌) (q : SimplexCategoryᵒᵖ) :
    H C x y |>.obj q := (SSet.const (X := 𝟙_ SSet.{v}) a).app q PUnit.unit

theorem vertexAt_id (x : C.Obj) (q : SimplexCategoryᵒᵖ) :
    vertexAt C (idVertex C x) q = (C.enriched.id x).app q PUnit.unit := by
  exact (congrFun ((C.enriched.id x).naturality (q.unop.const _ 0).op) PUnit.unit).symm

theorem vertexAt_comp {x y z : C.Obj} (a : H C x y _⦋0⦌) (b : H C y z _⦋0⦌)
    (q : SimplexCategoryᵒᵖ) :
    vertexAt C (compVertex C a b) q =
      (C.enriched.comp x y z).app q (vertexAt C a q, vertexAt C b q) := by
  exact (congrFun ((C.enriched.comp x y z).naturality (q.unop.const _ 0).op) (a, b)).symm

/-- Precomposition by the supplied original vertex, as a full simplicial map. -/
def pre {x' x : C.Obj} (a : H C x' x _⦋0⦌) (y : C.Obj) :
    H C x y ⟶ H C x' y := lift (SSet.const a) (𝟙 _) ≫ C.enriched.comp x' x y

/-- Postcomposition by the supplied original vertex, as a full simplicial map. -/
def post (x : C.Obj) {y y' : C.Obj} (b : H C y y' _⦋0⦌) :
    H C x y ⟶ H C x y' := lift (𝟙 _) (SSet.const b) ≫ C.enriched.comp x y y'

/-- The original map sending f to b composed with f composed with a. -/
def translation {x' x y y' : C.Obj} (a : H C x' x _⦋0⦌) (b : H C y y' _⦋0⦌) :
    H C x y ⟶ H C x' y' := pre C a y ≫ post C x' b

@[simp] theorem pre_app {x' x : C.Obj} (a : H C x' x _⦋0⦌) (y : C.Obj)
    (q : SimplexCategoryᵒᵖ) (f : (H C x y).obj q) :
    (pre C a y).app q f = (C.enriched.comp x' x y).app q (vertexAt C a q, f) := rfl

@[simp] theorem post_app (x : C.Obj) {y y' : C.Obj} (b : H C y y' _⦋0⦌)
    (q : SimplexCategoryᵒᵖ) (f : (H C x y).obj q) :
    (post C x b).app q f = (C.enriched.comp x y y').app q (f, vertexAt C b q) := rfl

@[simp] theorem translation_app {x' x y y' : C.Obj}
    (a : H C x' x _⦋0⦌) (b : H C y y' _⦋0⦌) (q : SimplexCategoryᵒᵖ)
    (f : (H C x y).obj q) :
    (translation C a b).app q f = (C.enriched.comp x' y y').app q
      ((C.enriched.comp x' x y).app q (vertexAt C a q, f), vertexAt C b q) := rfl

theorem translation_operator {x' x y y' : C.Obj}
    (a : H C x' x _⦋0⦌) (b : H C y y' _⦋0⦌)
    {q r : SimplexCategoryᵒᵖ} (α : q ⟶ r) (f : (H C x y).obj q) :
    (H C x' y').map α ((translation C a b).app q f) =
      (translation C a b).app r ((H C x y).map α f) :=
  (congrFun ((translation C a b).naturality α) f).symm

@[simp] theorem pre_id (x y : C.Obj) : pre C (idVertex C x) y = 𝟙 (H C x y) := by
  ext q f
  rw [pre_app, vertexAt_id]
  exact Category.id_comp (obj := SimplicialEnrichment.At C.Obj q) (X := x) (Y := y) f

@[simp] theorem post_id (x y : C.Obj) : post C x (idVertex C y) = 𝟙 (H C x y) := by
  ext q f
  rw [post_app, vertexAt_id]
  exact Category.comp_id (obj := SimplicialEnrichment.At C.Obj q) (X := x) (Y := y) f

theorem pre_comp {x₀ x₁ x₂ : C.Obj}
    (a : H C x₀ x₁ _⦋0⦌) (b : H C x₁ x₂ _⦋0⦌) (y : C.Obj) :
    pre C b y ≫ pre C a y = pre C (compVertex C a b) y := by
  ext q f
  simp only [SSet.comp_app, types_comp_apply, pre_app, vertexAt_comp]
  exact (Category.assoc (obj := SimplicialEnrichment.At C.Obj q)
    (W := x₀) (X := x₁) (Y := x₂) (Z := y) _ _ _).symm

theorem post_comp (x : C.Obj) {y₀ y₁ y₂ : C.Obj}
    (a : H C y₀ y₁ _⦋0⦌) (b : H C y₁ y₂ _⦋0⦌) :
    post C x a ≫ post C x b = post C x (compVertex C a b) := by
  ext q f
  simp only [SSet.comp_app, types_comp_apply, post_app, vertexAt_comp]
  exact Category.assoc (obj := SimplicialEnrichment.At C.Obj q)
    (W := x) (X := y₀) (Y := y₁) (Z := y₂) _ _ _

theorem pre_post {x' x y y' : C.Obj} (a : H C x' x _⦋0⦌) (b : H C y y' _⦋0⦌) :
    pre C a y ≫ post C x' b = post C x b ≫ pre C a y' := by
  ext q f
  simp only [SSet.comp_app, types_comp_apply, pre_app, post_app]
  exact Category.assoc (obj := SimplicialEnrichment.At C.Obj q)
    (W := x') (X := x) (Y := y) (Z := y') _ _ _

theorem translation_comp_inverse {x' x y y' : C.Obj}
    (a : H C x' x _⦋0⦌) (b : H C y y' _⦋0⦌)
    (abar : H C x x' _⦋0⦌) (bbar : H C y' y _⦋0⦌) :
    translation C a b ≫ translation C abar bbar =
      pre C (compVertex C abar a) y ≫ post C x (compVertex C b bbar) := by
  ext q f
  simp only [SSet.comp_app, types_comp_apply, translation_app, pre_app, post_app,
    vertexAt_comp]
  let aa : @Quiver.Hom (SimplicialEnrichment.At C.Obj q) _ x' x := vertexAt C a q
  let ab : @Quiver.Hom (SimplicialEnrichment.At C.Obj q) _ x x' := vertexAt C abar q
  let bb : @Quiver.Hom (SimplicialEnrichment.At C.Obj q) _ y y' := vertexAt C b q
  let bc : @Quiver.Hom (SimplicialEnrichment.At C.Obj q) _ y' y := vertexAt C bbar q
  change (ab ≫ ((aa ≫ f) ≫ bb)) ≫ bc = ((ab ≫ aa) ≫ f) ≫ (bb ≫ bc)
  simp only [Category.assoc]

variable {C} {D : SimplicialCat.{o₂, v}}

theorem vertexAt_map (F : EnrichedFunctor SSet.{v} C.Obj D.Obj) {x y : C.Obj}
    (a : H C x y _⦋0⦌) (q : SimplexCategoryᵒᵖ) :
    (F.map x y).app q (vertexAt C a q) =
      vertexAt D ((F.map x y).app (op ⦋0⦌) a) q :=
  congrFun ((F.map x y).naturality (q.unop.const _ 0).op) a

/-- Literal strict naturality of the original translation under every enriched functor. -/
theorem translation_naturality (F : EnrichedFunctor SSet.{v} C.Obj D.Obj)
    {x' x y y' : C.Obj} (a : H C x' x _⦋0⦌) (b : H C y y' _⦋0⦌) :
    translation C a b ≫ F.map x' y' = F.map x y ≫
      translation D ((F.map x' x).app (op ⦋0⦌) a) ((F.map y y').app (op ⦋0⦌) b) := by
  ext q f
  simp only [SSet.comp_app, types_comp_apply, translation_app]
  change (SimplicialEnrichment.functor F q).map
      ((vertexAt C a q ≫ f) ≫ vertexAt C b q) = _
  rw [Functor.map_comp, Functor.map_comp]
  dsimp only [SimplicialEnrichment.functor]
  rw [vertexAt_map, vertexAt_map]
  rfl

end

end DaggerOrdinaryTranslation
