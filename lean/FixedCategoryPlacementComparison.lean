import FixedCategoryConnectedColimits
import FixedCategoryGenerators
import FixedGraphPlacementChecks
import DaggerModels.TwoObjectDaggerCell
import DaggerModels.DaggerDiscreteObjects

/-! Compare the actual literal-O free placements with the original two-object dagger cells.
The original free map, path data, object functions and both diagonal copies are retained. -/

open CategoryTheory Limits DaggerModels DaggerFixedGraphPlacements
open DaggerFixedGraphPlacementData DaggerFixedGraphPlacementChecks
open DaggerFixedGraphGenerators DaggerFixedCategoryAdjunction
open DaggerFixedCategoryConnectedColimits

universe u

namespace DaggerFixedCategoryPlacementComparison

noncomputable section

variable {O : Type u}

def source : Position O → O
  | .inl p => p.val.1
  | .inr x => x

def target : Position O → O
  | .inl p => p.val.2
  | .inr x => x

def sigma (s : Position O) : TwoObjectDaggerGraph.Vertex.{u} → O
  | ⟨false⟩ => source s
  | ⟨true⟩ => target s

abbrev placed (s : Position O) (K : SSet.{u}) := (placement O s).obj K
abbrev freePlaced (s : Position O) (K : SSet.{u}) := (free O).obj (placed s K)

def zeta (s : Position O) (K : SSet.{u}) :
    K ⟶ (placed s K).Hom (source s) (target s) := by
  cases s with
  | inl p => exact (upperAdjunction O p).unit.app K
  | inr x => exact (diagonalAdjunction O x).unit.app K

def gamma (s : Position O) (K : SSet.{u}) :
    TwoObjectDaggerGraph.graph K ⟶ (placed s K).toGraph :=
  TwoObjectDaggerGraph.fromData (source s) (target s) (zeta s K)

def beta (s : Position O) (K : SSet.{u}) :
    TwoObjectDaggerCell.cell K ⟶ (freePlaced s K).toCat :=
  FreeDaggerSimplicialCategory.functor.map (gamma s K)

theorem beta_obj (s : Position O) (K : SSet.{u}) : (beta s K).obj = sigma s := by
  change (gamma s K).obj = sigma s
  funext v
  rcases v with ⟨v⟩
  cases v <;> rfl

theorem beta_forward (s : Position O) (K : SSet.{u}) :
    TwoObjectDaggerCell.generator K ≫ (beta s K).map
      TwoObjectDaggerGraph.left TwoObjectDaggerGraph.right =
        zeta s K ≫ FreeSimplicialPaths.inclusion (placed s K).toGraph (source s) (target s) := by
  ext n e
  change ((FreeDaggerSimplicialCategory.functor.map (gamma s K)).map
    TwoObjectDaggerGraph.left TwoObjectDaggerGraph.right).app n
    ((FreeSimplicialPaths.inclusion (TwoObjectDaggerGraph.graph K)
      TwoObjectDaggerGraph.left TwoObjectDaggerGraph.right).app n e) = _
  rw [FreeDaggerSimplicialCategory.functor_map_app]
  rfl

theorem beta_reverse (s : Position O) (K : SSet.{u}) :
    FreeSimplicialPaths.inclusion (TwoObjectDaggerGraph.graph K)
      TwoObjectDaggerGraph.right TwoObjectDaggerGraph.left ≫
        (beta s K).map TwoObjectDaggerGraph.right TwoObjectDaggerGraph.left =
          zeta s K ≫ (placed s K).dagger (source s) (target s) ≫
            FreeSimplicialPaths.inclusion (placed s K).toGraph (target s) (source s) := by
  ext n e
  change ((FreeDaggerSimplicialCategory.functor.map (gamma s K)).map _ _).app n
    ((FreeSimplicialPaths.inclusion (TwoObjectDaggerGraph.graph K) _ _).app n e) = _
  rw [FreeDaggerSimplicialCategory.functor_map_app]
  rfl

theorem beta_path (s : Position O) (K : SSet.{u}) (n : SimplexCategoryᵒᵖ)
    {x y : TwoObjectDaggerGraph.Vertex.{u}}
    (p : FreeSimplicialPaths.Path (TwoObjectDaggerGraph.graph K) n x y) :
    ((beta s K).map x y).app n p =
      (FreeDaggerSimplicialCategory.degreeMap (gamma s K) n).mapPath p :=
  FreeDaggerSimplicialCategory.functor_map_app _ n p

theorem upper_zeta (p : UpperIndex O) (K : SSet.{u}) :
    zeta (.inl p) K = eqToHom (upper_active p K).symm := by
  change (upperAdjunction O p).unit.app K = _
  change ((upperParameterAdjunction O p).comp
    (DaggerFixedGraph.fixedObjectDecomposition O).symm.toAdjunction).homEquiv K _ (𝟙 _) ≫
      𝟙 _ = _
  rw [Category.comp_id, Adjunction.comp_homEquiv]
  change (upperParameterAdjunction O p).homEquiv K _
    ((DaggerFixedGraph.fixedObjectDecomposition O).symm.toAdjunction.homEquiv
      ((upperParameterPlacement O p).obj K) _ (𝟙 _)) = _
  rw [Adjunction.homEquiv_id]
  unfold upperParameterAdjunction
  rw [Adjunction.comp_homEquiv]
  dsimp only
  unfold DaggerPlacementStructure.singleAdjunction DaggerPlacementStructure.includeLeftAdjunction
  rw [Adjunction.mkOfHomEquiv_homEquiv, Adjunction.mkOfHomEquiv_homEquiv]
  dsimp only
  change (DaggerPlacementStructure.singleAtIso p K).inv ≫
    ((DaggerFixedGraph.fixedObjectDecomposition O).counitIso.inv.app
      ((upperParameterPlacement O p).obj K)).1 p = _
  apply eq_of_heq
  simp [DaggerPlacementStructure.singleAtIso, DaggerPlacementStructure.single,
    DaggerPlacementStructure.singleObj, DaggerFixedGraph.fixedObjectDecomposition,
    DaggerFixedGraph.decomposition, DaggerFixedGraph.parametersEquivalence,
    DaggerFixedGraph.actionDecomposition, DaggerFixedGraph.counitIso,
    DaggerFixedGraph.counitParameterIso, DaggerFixedGraph.counitUpperIso]
  simp [upperParameterPlacement, DaggerPlacementStructure.includeLeft,
    DaggerPlacementStructure.single, DaggerPlacementStructure.singleObj]

theorem diagonal_zeta (x : O) (K : SSet.{u}) :
    zeta (.inr x) K = Sigma.ι (fun _ : DaggerFixedGraph.C2 ↦ K) 1 ≫
      (diagonalFiberIso x K).inv := by
  change (diagonalAdjunction O x).unit.app K = _
  change ((diagonalParameterAdjunction O x).comp
    (DaggerFixedGraph.fixedObjectDecomposition O).symm.toAdjunction).homEquiv K _ (𝟙 _) ≫
      𝟙 _ = _
  rw [Category.comp_id, Adjunction.comp_homEquiv]
  change (diagonalParameterAdjunction O x).homEquiv K _
    ((DaggerFixedGraph.fixedObjectDecomposition O).symm.toAdjunction.homEquiv
      ((diagonalParameterPlacement O x).obj K) _ (𝟙 _)) = _
  rw [Adjunction.homEquiv_id]
  unfold diagonalParameterAdjunction
  rw [Adjunction.comp_homEquiv]
  dsimp only
  rw [Adjunction.comp_homEquiv]
  dsimp only
  unfold DaggerPlacementStructure.singleAdjunction DaggerPlacementStructure.includeRightAdjunction
  rw [Adjunction.mkOfHomEquiv_homEquiv, Adjunction.mkOfHomEquiv_homEquiv]
  change DaggerFreeBC2.freeAdjunction.homEquiv K _
    ((DaggerPlacementStructure.singleAtIso x (DaggerFreeBC2.free.obj K)).inv ≫
      ((DaggerFixedGraph.fixedObjectDecomposition O).counitIso.inv.app
        ((diagonalParameterPlacement O x).obj K)).2 x) = _
  rw [DaggerFreeBC2.free_homEquiv]
  change Sigma.ι (fun _ : DaggerFixedGraph.C2 ↦ K) 1 ≫
    ((DaggerPlacementStructure.singleAtIso x (DaggerFreeBC2.free.obj K)).inv ≫
      ((DaggerFixedGraph.fixedObjectDecomposition O).counitIso.inv.app
        ((diagonalParameterPlacement O x).obj K)).2 x).app DaggerFreeBC2.point = _
  apply congrArg (fun f ↦ Sigma.ι (fun _ : DaggerFixedGraph.C2 ↦ K) 1 ≫ f)
  apply eq_of_heq
  simp [DaggerPlacementStructure.singleAtIso, DaggerPlacementStructure.single,
    DaggerPlacementStructure.singleObj, DaggerFixedGraph.fixedObjectDecomposition,
    DaggerFixedGraph.decomposition, DaggerFixedGraph.parametersEquivalence,
    DaggerFixedGraph.actionDecomposition, DaggerFixedGraph.counitIso,
    DaggerFixedGraph.counitParameterIso, DaggerFixedGraph.counitDiagonalIso, diagonalFiberIso]
  simp [diagonalParameterPlacement, DaggerPlacementStructure.includeRight,
    DaggerPlacementStructure.single, DaggerPlacementStructure.singleObj]

/-- The actual placement Hom equivalence, with its original singleton/C₂ unit. -/
def edgeHomEquiv (s : Position O) (K : SSet.{u}) (G : FixedDaggerSimplicialGraph O) :
    (placed s K ⟶ G) ≃ (K ⟶ G.Hom (source s) (target s)) := by
  cases s with
  | inl p => exact (upperAdjunction O p).homEquiv K G
  | inr x => exact (diagonalAdjunction O x).homEquiv K G

theorem edgeHomEquiv_apply (s : Position O) (K : SSet.{u})
    {G : FixedDaggerSimplicialGraph O} (f : placed s K ⟶ G) :
    edgeHomEquiv s K G f = zeta s K ≫ f.map (source s) (target s) := by
  cases s with
  | inl p => exact (upperAdjunction O p).homEquiv_apply K G f
  | inr x => exact (diagonalAdjunction O x).homEquiv_apply K G f

/-- Arbitrary ambient object maps are retained, using the accepted original reindex adapter. -/
def ambientHomEquiv (B : FixedDaggerSimplicialCat O) (C : DaggerSimplicialCat.{u, u}) :
    (B.toCat ⟶ C) ≃ (Σ φ : O → C.Obj, B ⟶ reindex C φ) where
  toFun F := ⟨F.obj, liftHom F rfl⟩
  invFun q := q.2.val ≫ inclusion C q.1
  left_inv F := liftHom_comp_inclusion F rfl
  right_inv q := by
    rcases q with ⟨φ, ⟨⟨⟨obj, map, map_id, map_comp⟩, map_dagger⟩, h⟩⟩
    cases h
    apply Sigma.ext
    · rfl
    · let f : B ⟶ reindex C φ :=
        ⟨{ obj := id
           map := map
           map_id := map_id
           map_comp := map_comp
           map_dagger := map_dagger }, rfl⟩
      exact heq_of_eq (liftHom_inclusion f)

/-- Full unrestricted ambient Hom classification for the actual literal-O free placement. -/
def fullHomEquiv (s : Position O) (K : SSet.{u}) (C : DaggerSimplicialCat.{u, u}) :
    ((freePlaced s K).toCat ⟶ C) ≃
      (Σ φ : O → C.Obj, K ⟶ C.enriched.Hom (φ (source s)) (φ (target s))) :=
  (ambientHomEquiv (freePlaced s K) C).trans (Equiv.sigmaCongrRight (fun φ ↦
    ((adjunction O).homEquiv (placed s K) (reindex C φ)).trans
      (edgeHomEquiv s K (reindex C φ).underlyingGraph)))

theorem fullHomEquiv_apply (s : Position O) (K : SSet.{u}) (C : DaggerSimplicialCat.{u, u})
    (F : (freePlaced s K).toCat ⟶ C) :
    fullHomEquiv s K C F = ⟨F.obj, zeta s K ≫
      FreeSimplicialPaths.inclusion (placed s K).toGraph (source s) (target s) ≫
        F.map (source s) (target s)⟩ := by
  apply Sigma.ext
  · rfl
  · apply heq_of_eq
    change edgeHomEquiv s K (reindex C F.obj).underlyingGraph
      ((adjunction O).homEquiv (placed s K) (reindex C F.obj) (liftHom F rfl)) = _
    rw [edgeHomEquiv_apply, adjunction_homEquiv]
    rfl

theorem fullHomEquiv_left_inv (s : Position O) (K : SSet.{u}) (C : DaggerSimplicialCat.{u, u})
    (F : (freePlaced s K).toCat ⟶ C) :
    (fullHomEquiv s K C).symm (fullHomEquiv s K C F) = F :=
  (fullHomEquiv s K C).left_inv F

theorem fullHomEquiv_right_inv (s : Position O) (K : SSet.{u}) (C : DaggerSimplicialCat.{u, u})
    (q : Σ φ : O → C.Obj, K ⟶ C.enriched.Hom (φ (source s)) (φ (target s))) :
    fullHomEquiv s K C ((fullHomEquiv s K C).symm q) = q :=
  (fullHomEquiv s K C).right_inv q

theorem beta_classify (s : Position O) (K : SSet.{u}) (C : DaggerSimplicialCat.{u, u})
    (F : (freePlaced s K).toCat ⟶ C) :
    TwoObjectDaggerCell.homEquiv K C (beta s K ≫ F) =
      ⟨(fullHomEquiv s K C F).1 (source s), (fullHomEquiv s K C F).1 (target s),
        (fullHomEquiv s K C F).2⟩ := by
  rw [fullHomEquiv_apply, TwoObjectDaggerCell.homEquiv_apply]
  change (⟨F.obj (source s), F.obj (target s),
    TwoObjectDaggerCell.generator K ≫ ((beta s K).map _ _ ≫ F.map _ _)⟩ :
      Σ x : C.Obj, Σ y : C.Obj, K ⟶ C.enriched.Hom x y) = _
  rw [← Category.assoc, beta_forward, Category.assoc]
  rfl

theorem zeta_naturality (s : Position O) {K L : SSet.{u}} (i : K ⟶ L) :
    i ≫ zeta s L = zeta s K ≫ ((placement O s).map i).map (source s) (target s) := by
  cases s with
  | inl p => exact upper_unit_naturality p i
  | inr x => exact diagonal_unit_naturality x i

theorem gamma_naturality (s : Position O) {K L : SSet.{u}} (i : K ⟶ L) :
    TwoObjectDaggerGraph.functor.map i ≫ gamma s L = gamma s K ≫
      FixedDaggerSimplicialGraph.toGraphMap ((placement O s).map i) := by
  apply (TwoObjectDaggerGraph.homEquiv K (placed s L).toGraph).injective
  change (⟨source s, target s, i ≫ zeta s L⟩ :
    Σ x : O, Σ y : O, K ⟶ (placed s L).Hom x y) =
      ⟨source s, target s, zeta s K ≫ ((placement O s).map i).map (source s) (target s)⟩
  rw [zeta_naturality]

theorem beta_naturality (s : Position O) {K L : SSet.{u}} (i : K ⟶ L) :
    TwoObjectDaggerCell.functor.map i ≫ beta s L = beta s K ≫
      ((free O).map ((placement O s).map i)).val := by
  change FreeDaggerSimplicialCategory.functor.map (TwoObjectDaggerGraph.functor.map i) ≫
    FreeDaggerSimplicialCategory.functor.map (gamma s L) =
      FreeDaggerSimplicialCategory.functor.map (gamma s K) ≫
        FreeDaggerSimplicialCategory.functor.map
          (FixedDaggerSimplicialGraph.toGraphMap ((placement O s).map i))
  rw [← Functor.map_comp, ← Functor.map_comp, gamma_naturality]

/-- The original discrete vertex maps, with no identification of the two cell objects. -/
def cellVertices (K : SSet.{u}) :
    DaggerDiscreteObjects.discrete TwoObjectDaggerGraph.Vertex.{u} ⟶ TwoObjectDaggerCell.cell K :=
  DaggerDiscreteObjects.lift _ _ id

def objectMap (s : Position O) :
    DaggerDiscreteObjects.discrete TwoObjectDaggerGraph.Vertex.{u} ⟶
      DaggerDiscreteObjects.discrete O := DaggerDiscreteObjects.lift _ _ (sigma s)

def placedVertices (s : Position O) (K : SSet.{u}) :
    DaggerDiscreteObjects.discrete O ⟶ (freePlaced s K).toCat :=
  DaggerDiscreteObjects.lift _ _ id

theorem objectGluing_condition (s : Position O) (K : SSet.{u}) :
    cellVertices K ≫ beta s K = objectMap s ≫ placedVertices s K := by
  apply (DaggerDiscreteObjects.homEquiv _ _).injective
  exact beta_obj s K

private def selectData (s : Position O) (K : SSet.{u}) (C : DaggerSimplicialCat.{u, u})
    (q : Σ φ : O → C.Obj, K ⟶ C.enriched.Hom (φ (source s)) (φ (target s))) :
    Σ x : C.Obj, Σ y : C.Obj, K ⟶ C.enriched.Hom x y :=
  ⟨q.1 (source s), q.1 (target s), q.2⟩

private theorem selectData_injective (s : Position O) (K : SSet.{u})
    (C : DaggerSimplicialCat.{u, u})
    (q r : Σ φ : O → C.Obj, K ⟶ C.enriched.Hom (φ (source s)) (φ (target s)))
    (hobj : q.1 = r.1) (hedge : selectData s K C q = selectData s K C r) : q = r := by
  rcases q with ⟨φ, t⟩
  rcases r with ⟨ψ, v⟩
  dsimp only at hobj
  cases hobj
  have ht : t = v := by simpa [selectData] using hedge
  cases ht
  rfl

/-- Source naturality retains the entire original fixed free-map and ambient target map. -/
theorem fullHomEquiv_naturality_left (s : Position O) {K L : SSet.{u}} (i : K ⟶ L)
    (C : DaggerSimplicialCat.{u, u}) (F : (freePlaced s L).toCat ⟶ C) :
    fullHomEquiv s K C (((free O).map ((placement O s).map i)).val ≫ F) =
      ⟨(fullHomEquiv s L C F).1, i ≫ (fullHomEquiv s L C F).2⟩ := by
  apply selectData_injective
  · rfl
  · dsimp only [selectData]
    rw [← beta_classify, ← Category.assoc, ← beta_naturality, Category.assoc,
      TwoObjectDaggerCell.homEquiv_naturality_left, beta_classify]

/-- Target naturality retains arbitrary object functions and all original enriched maps. -/
theorem fullHomEquiv_naturality_right (s : Position O) (K : SSet.{u})
    {C D : DaggerSimplicialCat.{u, u}} (F : (freePlaced s K).toCat ⟶ C) (H : C ⟶ D) :
    fullHomEquiv s K D (F ≫ H) =
      ⟨H.obj ∘ (fullHomEquiv s K C F).1,
        (fullHomEquiv s K C F).2 ≫ H.map _ _⟩ := by
  apply selectData_injective
  · rfl
  · dsimp only [selectData]
    rw [← beta_classify, ← Category.assoc,
      TwoObjectDaggerCell.homEquiv_naturality_right, beta_classify]
    rfl

/-- The commutativity equation retains the complete original ambient object function. -/
theorem gluingObjectEq (s : Position O) (K : SSet.{u})
    (q : PushoutCocone (cellVertices K) (objectMap s)) :
    q.inl.obj = q.inr.obj ∘ sigma s :=
  congrArg (fun F ↦ F.obj) q.condition

/-- Transport only the original generator's endpoint types, retaining its entire SSet map. -/
def gluingData (s : Position O) (K : SSet.{u})
    (q : PushoutCocone (cellVertices K) (objectMap s)) :
    Σ φ : O → q.pt.Obj, K ⟶ q.pt.enriched.Hom (φ (source s)) (φ (target s)) :=
  ⟨q.inr.obj, TwoObjectDaggerCell.generator K ≫ q.inl.map _ _ ≫ eqToHom
    (congrArg₂ q.pt.enriched.Hom (congrFun (gluingObjectEq s K q) TwoObjectDaggerGraph.left)
      (congrFun (gluingObjectEq s K q) TwoObjectDaggerGraph.right))⟩

private theorem edgeData_transport (C : DaggerSimplicialCat.{u, u}) (K : SSet.{u})
    (a b a' b' : C.Obj) (ha : a = a') (hb : b = b') (t : K ⟶ C.enriched.Hom a b) :
    (⟨a', b', t ≫ eqToHom (congrArg₂ C.enriched.Hom ha hb)⟩ :
      Σ x : C.Obj, Σ y : C.Obj, K ⟶ C.enriched.Hom x y) = ⟨a, b, t⟩ := by
  cases ha
  cases hb
  simp

theorem gluingData_classify (s : Position O) (K : SSet.{u})
    (q : PushoutCocone (cellVertices K) (objectMap s)) :
    selectData s K q.pt (gluingData s K q) = TwoObjectDaggerCell.homEquiv K q.pt q.inl := by
  simpa only [selectData, gluingData, TwoObjectDaggerCell.homEquiv_apply] using
    edgeData_transport q.pt K _ _ _ _
      (congrFun (gluingObjectEq s K q) TwoObjectDaggerGraph.left)
      (congrFun (gluingObjectEq s K q) TwoObjectDaggerGraph.right)
      (TwoObjectDaggerCell.generator K ≫ q.inl.map _ _)

/-- The same literal-O free apex, with the full arbitrary ambient descended dagger functor. -/
def gluingDesc (s : Position O) (K : SSet.{u})
    (q : PushoutCocone (cellVertices K) (objectMap s)) : (freePlaced s K).toCat ⟶ q.pt :=
  (fullHomEquiv s K q.pt).symm (gluingData s K q)

theorem gluingDesc_fac_left (s : Position O) (K : SSet.{u})
    (q : PushoutCocone (cellVertices K) (objectMap s)) :
    beta s K ≫ gluingDesc s K q = q.inl := by
  apply (TwoObjectDaggerCell.homEquiv K q.pt).injective
  rw [beta_classify]
  change selectData s K q.pt
    (fullHomEquiv s K q.pt ((fullHomEquiv s K q.pt).symm (gluingData s K q))) = _
  rw [fullHomEquiv_right_inv]
  exact gluingData_classify s K q

theorem gluingDesc_fac_right (s : Position O) (K : SSet.{u})
    (q : PushoutCocone (cellVertices K) (objectMap s)) :
    placedVertices s K ≫ gluingDesc s K q = q.inr := by
  apply (DaggerDiscreteObjects.homEquiv O q.pt).injective
  exact congrArg Sigma.fst (fullHomEquiv_right_inv s K q.pt (gluingData s K q))

theorem gluingDesc_unique (s : Position O) (K : SSet.{u})
    (q : PushoutCocone (cellVertices K) (objectMap s)) (m : (freePlaced s K).toCat ⟶ q.pt)
    (hl : beta s K ≫ m = q.inl) (hr : placedVertices s K ≫ m = q.inr) :
    m = gluingDesc s K q := by
  apply (fullHomEquiv s K q.pt).injective
  apply selectData_injective
  · exact congrArg (fun F ↦ F.obj) (hr.trans (gluingDesc_fac_right s K q).symm)
  · dsimp only [selectData]
    rw [← beta_classify, ← beta_classify, hl, gluingDesc_fac_left]

/-- Actual discrete-object gluing, including both legs and the full universal property. -/
def objectGluing (s : Position O) (K : SSet.{u}) :
    IsPushout (cellVertices K) (objectMap s) (beta s K) (placedVertices s K) :=
  IsPushout.of_isColimit (PushoutCocone.IsColimit.mk (objectGluing_condition s K)
    (gluingDesc s K) (gluingDesc_fac_left s K) (gluingDesc_fac_right s K)
    (gluingDesc_unique s K))

theorem cellVertices_naturality {K L : SSet.{u}} (i : K ⟶ L) :
    cellVertices K ≫ TwoObjectDaggerCell.functor.map i = cellVertices L := by
  apply (DaggerDiscreteObjects.homEquiv _ _).injective
  rfl

theorem placedVertices_naturality (s : Position O) {K L : SSet.{u}} (i : K ⟶ L) :
    placedVertices s K ≫ ((free O).map ((placement O s).map i)).val = placedVertices s L := by
  apply (DaggerDiscreteObjects.homEquiv _ _).injective
  exact ((free O).map ((placement O s).map i)).property

/-- Horizontal cancellation uses the two original object-gluing pushouts. -/
theorem placementSquare (s : Position O) {K L : SSet.{u}} (i : K ⟶ L) :
    IsPushout (TwoObjectDaggerCell.functor.map i) (beta s K) (beta s L)
      ((free O).map ((placement O s).map i)).val := by
  apply ((objectGluing s K).paste_horiz_iff (beta_naturality s i)).mp
  rw [cellVertices_naturality, placedVertices_naturality]
  exact objectGluing s L

/-- Paste onto the same actual fixed free-cell pushout, retaining all four original maps. -/
theorem cellPushout (s : Position O) {K L : SSet.{u}} (i : K ⟶ L)
    {C D : FixedDaggerSimplicialCat O} (a : freePlaced s K ⟶ C) (b : freePlaced s L ⟶ D)
    (f : C ⟶ D) (sq : IsPushout ((free O).map ((placement O s).map i)) a b f) :
    IsPushout (TwoObjectDaggerCell.functor.map i) (beta s K ≫ a.val)
      (beta s L ≫ b.val) f.val :=
  (placementSquare s i).paste_vert (map_isPushout sq)

end

end DaggerFixedCategoryPlacementComparison
