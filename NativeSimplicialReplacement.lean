import NativeSimplicialReplacementCells

/-! The full simplicial replacement, its original chain projection, and augmentations. -/
set_option autoImplicit false
open CategoryTheory Limits Opposite HomotopicalAlgebra
open DaggerNativeSimplicialReplacementCells DaggerOriginalProductGadget DaggerSSetGluing
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerNativeSimplicialReplacement
noncomputable section

variable {C : Type u} [Category.{u} C] (G : C ⥤ SSet.{u})

/-- The row contains every original chain and every entire first-object simplex. -/
def replacement : SimplicialObject SSet.{u} where
  obj q := familySSet (family G q)
  map {q r} α :=
    { app k := horizontal G α k
      naturality {k l} β := by funext x; exact operators_commute G α β x }
  map_id q := by
    apply NatTrans.ext
    funext k x
    exact horizontal_id G q k x
  map_comp α β := by
    apply NatTrans.ext
    funext k x
    exact horizontal_comp G α β k x

/-- Forget only the parameter simplex, retaining the entire original chain. -/
def projection : replacement G ⟶ DaggerNerveTheoremA.outerDegreeConstant (nerve C) where
  app q := familyProjection (family G q)
  naturality {q r} α := by apply NatTrans.ext; rfl

theorem projection_row_GW (hG : ∀ c, GW (pointMap (G.obj c)))
    (q : SimplexCategoryᵒᵖ) : GW ((projection G).app q) :=
  familyProjection_GW (family G q) (fun c ↦ hG (first c))

def diagonalProjection : DaggerBisimplicialDiagonal.diag (replacement G) ⟶ nerve C :=
  DaggerBisimplicialDiagonal.diagMap (projection G) ≫
    eqToHom (DaggerNerveTheoremA.diag_outerDegreeConstant (nerve C))

/-- Native rowwise weak equivalences give the weak comparison to the actual full nerve. -/
theorem diagonalProjection_GW (hG : ∀ c, GW (pointMap (G.obj c))) :
    GW (diagonalProjection G) := by
  have : WeakEquivalence (DaggerBisimplicialDiagonal.diagMap (projection G)) :=
    (weakEquivalence_iff_GW _).mpr
      (DaggerOriginalDiagonalGeometric.diagMap_geometric_row (projection G)
        (projection_row_GW G hG))
  apply (weakEquivalence_iff_GW _).mp
  dsimp only [diagonalProjection]
  infer_instance

/-- A natural augmentation applies its literal full map to the entire parameter simplex. -/
def augmentation {X : SSet.{u}} (η : G ⟶ (Functor.const C).obj X) :
    replacement G ⟶ (Functor.const SimplexCategoryᵒᵖ).obj X where
  app q :=
    { app k x := (η.app (first x.1)).app k x.2
      naturality {k l} β := by
        funext x
        exact congrFun ((η.app (first x.1)).naturality β) x.2 }
  naturality {q r} α := by
    apply NatTrans.ext
    funext k x
    have h := η.naturality (initialArrow α x.1)
    change G.map (initialArrow α x.1) ≫ η.app (first ((nerve C).map α x.1)) =
      η.app (first x.1) ≫ 𝟙 X at h
    exact congrFun (NatTrans.congr_app (h.trans
      (Category.comp_id (η.app (first x.1)))) k) x.2

/-- The original augmentation is retained on every diagonal cell. -/
def diagonalAugmentation {X : SSet.{u}} (η : G ⟶ (Functor.const C).obj X) :
    DaggerBisimplicialDiagonal.diag (replacement G) ⟶ X where
  app q x := (η.app (first x.1)).app q x.2
  naturality {q r} α := by
    funext x
    have h := congrFun (NatTrans.congr_app ((augmentation G η).naturality α) q) x
    have v := congrFun (((augmentation G η).app r).naturality α) (horizontal G α q x)
    exact v.trans (congrArg (X.map α) h)

end
end DaggerNativeSimplicialReplacement
