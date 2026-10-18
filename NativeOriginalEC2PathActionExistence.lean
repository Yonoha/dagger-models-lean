import NativeOriginalEC2BasedCotensorEdges
import NativeOriginalLeftPathInvolutionAction

/-! The SAME native fixed-endpoint path action detects the SAME old canonical components. -/
set_option autoImplicit false
open CategoryTheory Opposite Simplicial HomotopicalAlgebra
open DaggerOriginalDaggerRealizationC2Action DaggerOriginalCompletedDaggerMappingAction
open DaggerOriginalEC2SimplicialAction DaggerOriginalSimplicialEquivariantParameterTensor
open DaggerOriginalSimplicialEquivariantEnrichedAdjunction
open DaggerOriginalFullVertexSubcomplex DaggerNativeOriginalEquivariantCotensorAdjunction
open DaggerNativeOriginalEC2BasedCotensorEdges DaggerNativeOriginalEC2RealizationUnitComparison
open DaggerNativeOriginalC2RealizationMapping
open scoped SSet.modelCategoryQuillen DaggerOriginalSimplicialActionModelCategory
universe u
namespace DaggerNativeOriginalEC2PathActionExistence
noncomputable section

variable (A : Action SSet.{u} C2.{u}) (s : A.V ⟶ A.V) (hs : s ≫ s = 𝟙 A.V)
variable (x y : A.V _⦋0⦌)
variable (hx : ∀ g, (A.ρ g).asHom.app (op ⦋0⦌) x = x)
variable (hy : ∀ g, (A.ρ g).asHom.app (op ⦋0⦌) y = y)

abbrev pathAction (hgen : (A.ρ generator).asHom = s) :=
  DaggerNativeOriginalLeftPathInvolutionAction.pathAction s hs x y
    (by rw [← hgen]; exact hx generator) (by rw [← hgen]; exact hy generator)

def inclusionAction (hgen : (A.ρ generator).asHom = s) :
    pathAction A s hs x y hx hy hgen ⟶ cotensorAction Δ[1] A where
  hom := (strictPathFiber A.V x y).ι
  comm g := by
    rcases originalC2_cases g with rfl | rfl
    · rw [MonoidHom.map_one, MonoidHom.map_one]
      change 𝟙 _ ≫ _ = _ ≫ 𝟙 _
      rw [Category.id_comp, Category.comp_id]
    · change ((pathAction A s hs x y hx hy hgen).ρ generator).asHom ≫ _ =
        (strictPathFiber A.V x y).ι ≫ (ihom Δ[1]).map ((A.ρ generator).asHom)
      rw [hgen]
      exact DaggerNativeOriginalLeftPathInvolutionAction.path_generator_ι s hs x y _ _

theorem path_iota_zero : (strictPathFiber A.V x y).ι ≫ A.V.pathEv₀ = SSet.const x := by
  have h := SSet.Subcomplex.fiber_ι_comp A.V.pathEv₀₁ (x, y)
  apply NatTrans.ext
  funext n v
  exact congrArg Prod.fst (congrFun (NatTrans.congr_app h n) v)

theorem path_iota_one : (strictPathFiber A.V x y).ι ≫ A.V.pathEv₁ = SSet.const y := by
  have h := SSet.Subcomplex.fiber_ι_comp A.V.pathEv₀₁ (x, y)
  apply NatTrans.ext
  funext n v
  exact congrArg Prod.snd (congrFun (NatTrans.congr_app h n) v)

def basedHomOfPathMap (hgen : (A.ρ generator).asHom = s)
    (f : simplicialAction ⟶ pathAction A s hs x y hx hy hgen) : BasedHom A x y :=
  ⟨f ≫ inclusionAction A s hs x y hx hy hgen, by
    constructor
    · change f.hom ≫ (strictPathFiber A.V x y).ι ≫ A.V.pathEv₀ = _
      rw [path_iota_zero, SSet.comp_const]
    · change f.hom ≫ (strictPathFiber A.V x y).ι ≫ A.V.pathEv₁ = _
      rw [path_iota_one, SSet.comp_const]⟩

def pathMapOfBasedHom (hgen : (A.ρ generator).asHom = s) (f : BasedHom A x y) :
    simplicialAction ⟶ pathAction A s hs x y hx hy hgen := by
  let l : simplicialAction.V ⟶ (strictPathFiber A.V x y).toSSet :=
    SSet.Subcomplex.lift f.val.hom (by
      change SSet.Subcomplex.range f.val.hom ≤ SSet.Subcomplex.fiber A.V.pathEv₀₁ (x, y)
      rw [SSet.Subcomplex.range_le_fiber_iff]
      apply NatTrans.ext
      funext n v
      apply Prod.ext
      · exact congrFun (NatTrans.congr_app f.property.1 n) v
      · exact congrFun (NatTrans.congr_app f.property.2 n) v)
  have hl : l ≫ (strictPathFiber A.V x y).ι = f.val.hom := SSet.Subcomplex.lift_ι _ _
  refine ⟨l, ?_⟩
  intro g
  apply (cancel_mono (strictPathFiber A.V x y).ι).mp
  have hj := (inclusionAction A s hs x y hx hy hgen).comm g
  change (simplicialAction.ρ g).asHom ≫ l ≫ (strictPathFiber A.V x y).ι =
    l ≫ ((pathAction A s hs x y hx hy hgen).ρ g).asHom ≫ (strictPathFiber A.V x y).ι
  change ((pathAction A s hs x y hx hy hgen).ρ g).asHom ≫ (strictPathFiber A.V x y).ι =
    (strictPathFiber A.V x y).ι ≫ ((cotensorAction Δ[1] A).ρ g).asHom at hj
  rw [hl, hj, ← Category.assoc, hl]
  exact f.val.comm g

theorem path_maps_nonempty_iff_based (hgen : (A.ρ generator).asHom = s) :
    Nonempty (simplicialAction ⟶ pathAction A s hs x y hx hy hgen) ↔ Nonempty (BasedHom A x y) :=
  ⟨fun ⟨f⟩ ↦ ⟨basedHomOfPathMap A s hs x y hx hy hgen f⟩,
    fun ⟨f⟩ ↦ ⟨pathMapOfBasedHom A s hs x y hx hy hgen f⟩⟩

def zeroProjection : simplicialParameterTensor simplicialAction.{u} Δ[0] ⟶ simplicialAction where
  hom := { app _ p := p.1, naturality _ _ _ := rfl }
  comm _g := by ext n p; rfl

def zeroSection : simplicialAction.{u} ⟶ simplicialParameterTensor simplicialAction Δ[0] where
  hom :=
    { app n e := (e, SSet.stdSimplex.const 0 0 n)
      naturality _ _ _ := by funext e; exact Prod.ext rfl (Subsingleton.elim _ _) }
  comm _g := by ext n e; exact Prod.ext rfl (Subsingleton.elim _ _)

theorem enriched_vertices_nonempty_iff_maps (B : Action SSet.{u} C2.{u}) :
    Nonempty ((enrichedMapping simplicialAction B) _⦋0⦌) ↔ Nonempty (simplicialAction ⟶ B) :=
  ⟨fun ⟨v⟩ ↦ ⟨zeroSection ≫ v⟩, fun ⟨f⟩ ↦ ⟨zeroProjection ≫ f⟩⟩

theorem enriched_path_vertices_iff [A.V.KanComplex] (hgen : (A.ρ generator).asHom = s) :
    Nonempty ((enrichedMapping simplicialAction (pathAction A s hs x y hx hy hgen)) _⦋0⦌) ↔
      SSet.π₀.mk (DaggerNativeOriginalActionCanonicalConstants.canonicalZero A x hx) =
        SSet.π₀.mk (DaggerNativeOriginalActionCanonicalConstants.canonicalZero A y hy) :=
  (enriched_vertices_nonempty_iff_maps _).trans
    ((path_maps_nonempty_iff_based A s hs x y hx hy hgen).trans
      (basedHom_nonempty_iff_canonical_components A x y hx hy))

theorem realized_path_vertices_iff [A.V.KanComplex] (hgen : (A.ρ generator).asHom = s) :
    Nonempty ((mappingFunctor.obj (pathAction A s hs x y hx hy hgen)) _⦋0⦌) ↔
      SSet.π₀.mk (DaggerNativeOriginalActionCanonicalConstants.canonicalZero A x hx) =
        SSet.π₀.mk (DaggerNativeOriginalActionCanonicalConstants.canonicalZero A y hy) := by
  let P := pathAction A s hs x y hx hy hgen
  have : P.V.KanComplex := strictPathFiber_fibrant A.V x y
  have : IsFibrant P :=
    (DaggerOriginalSimplicialActionModelCategory.isFibrant_iff_underlying _).2 inferInstance
  have : (enrichedMapping simplicialAction P).KanComplex :=
    DaggerOriginalCompletedDaggerDerivedMapping.enrichedMapping_kan simplicialAction P
  have : WeakEquivalence (comparison P) := comparison_weak P
  exact (DaggerOriginalStrictPathFiberVertices.vertices_nonempty_iff_of_weakEquivalence
    (comparison P)).symm.trans (enriched_path_vertices_iff A s hs x y hx hy hgen)

end
end DaggerNativeOriginalEC2PathActionExistence
