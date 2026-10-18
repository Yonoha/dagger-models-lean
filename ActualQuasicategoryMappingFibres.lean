import NativeNonfinalLiftingKanFibres
import OriginalAllPrefixBoundaryProjectionLifting

/-! Native mapping fibres for EVERY original quasi-category and every original prefix simplex. -/
set_option autoImplicit false
open CategoryTheory Limits Opposite Simplicial
open DaggerOriginalSimplexCoslice DaggerOriginalOrdinalJoinLeft
open DaggerOriginalJoinedBoundaryRestriction DaggerOriginalJoinedBoundaryProjection
open DaggerNativeNonfinalLiftingKanFibres
universe u
namespace DaggerActualQuasicategoryMappingFibres
noncomputable section

def prefixMapping (X : SSet.{u}) (k : SimplexCategory) (σ : X.obj (op k))
    (b : X.obj (op ⦋0⦌)) : SSet.{u} :=
  (SSet.Subcomplex.fiber (cosliceProjection k X σ) b : SSet.{u})

abbrev leftMapping (X : SSet.{u}) (a b : X.obj (op ⦋0⦌)) : SSet.{u} :=
  prefixMapping X ⦋0⦌ a b

theorem projection_nonfinal (X : SSet.{u}) [X.Quasicategory] (k : ℕ)
    (σ : X.obj (op ⦋k⦌)) : NonfinalLifting (cosliceProjection ⦋k⦌ X σ) := by
  intro n i hi
  have hX : DaggerOriginalInnerHornFillers.innerHornFillers X :=
    DaggerNativeHoIsoTriangles.native_inner_fillers X
  rw [← cosliceBoundaryRestriction_comp_projection k X σ]
  have := DaggerOriginalCosliceLeftLiftingProperty.coslice_hasLiftingProperty hX k n i hi σ
  have := DaggerOriginalAllPrefixBoundaryProjectionLifting.boundaryProjection_hasLiftingProperty
    hX k n i hi
  infer_instance

theorem prefixMapping_kan (X : SSet.{u}) [X.Quasicategory] (k : ℕ)
    (σ : X.obj (op ⦋k⦌)) (b : X.obj (op ⦋0⦌)) :
    (prefixMapping X ⦋k⦌ σ b).KanComplex :=
  fiber_kan _ b (projection_nonfinal X k σ)

theorem leftMapping_kan (X : SSet.{u}) [X.Quasicategory] (a b : X.obj (op ⦋0⦌)) :
    (leftMapping X a b).KanComplex := prefixMapping_kan X 0 a b

def cosliceMap {X Y : SSet.{u}} (f : X ⟶ Y) (k : SimplexCategory) (σ : X.obj (op k)) :
    simplexCoslice k X σ ⟶ simplexCoslice k Y (f.app (op k) σ) where
  app q s := ⟨f.app (op ((ordinalJoinLeft k).obj q.unop)) s.val, by
    exact (congrFun (f.naturality (AugmentedSimplexCategory.inl' k q.unop).op) s.val).symm.trans
      (congrArg (f.app (op k)) s.property)⟩
  naturality q r α := by
    funext s
    apply Subtype.ext
    exact congrFun (f.naturality ((ordinalJoinLeft k).map α.unop).op) s.val

theorem projection_natural {X Y : SSet.{u}} (f : X ⟶ Y) (k : SimplexCategory)
    (σ : X.obj (op k)) : cosliceMap f k σ ≫ cosliceProjection k Y (f.app (op k) σ) =
      cosliceProjection k X σ ≫ f := by
  apply NatTrans.ext
  funext q s
  exact (congrFun (f.naturality (AugmentedSimplexCategory.inr' k q.unop).op) s.val).symm

def map {X Y : SSet.{u}} (f : X ⟶ Y) (k : SimplexCategory) (σ : X.obj (op k))
    (b : X.obj (op ⦋0⦌)) :
    prefixMapping X k σ b ⟶ prefixMapping Y k (f.app (op k) σ) (f.app (op ⦋0⦌) b) :=
  SSet.Subcomplex.mapFiber (cosliceProjection k X σ)
    (cosliceProjection k Y (f.app (op k) σ)) (cosliceMap f k σ) f
    (projection_natural f k σ) b (f.app (op ⦋0⦌) b) rfl

theorem map_id (X : SSet.{u}) (k : SimplexCategory) (σ : X.obj (op k))
    (b : X.obj (op ⦋0⦌)) : map (𝟙 X) k σ b = 𝟙 (prefixMapping X k σ b) := by
  apply NatTrans.ext
  funext q s
  apply Subtype.ext
  apply Subtype.ext
  rfl

theorem map_comp {X Y Z : SSet.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (k : SimplexCategory)
    (σ : X.obj (op k)) (b : X.obj (op ⦋0⦌)) :
    map (f ≫ g) k σ b = map f k σ b ≫ map g k (f.app (op k) σ) (f.app (op ⦋0⦌) b) := by
  apply NatTrans.ext
  funext q s
  apply Subtype.ext
  apply Subtype.ext
  rfl

end
end DaggerActualQuasicategoryMappingFibres
