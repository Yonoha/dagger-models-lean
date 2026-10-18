import OriginalGateChainHomIso

set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory Opposite Simplicial
open DaggerChosenRigidificationNecklace
open DaggerOriginalFlagFlankification
open DaggerChosenRigidificationNecklace.NecklaceCode

universe u

namespace DaggerOriginalProductGadget

noncomputable section

attribute [local instance] Classical.propDecidable

variable {X : SSet.{u}}
  (R : X.obj (op ⦋0⦌) → X.obj (op ⦋0⦌) → Prop)
  (hrefl : ∀ x, R x x)
  (htrans : ∀ {x y z}, R x y → R y z → R x z)
  (hanti : ∀ {x y}, R x y → R y x → x = y)
  (hbound : ∀ {a b} {q : SimplexCategoryᵒᵖ} (x : (flagHom X a b).obj q) w,
    w ∈ flagVertexSupport x → R a w ∧ R w b)
  (hm : ∀ {a b} (P : NecklacesOver X a b),
    (∀ c : P.code.Bead, beadElement P c ∈ X.nonDegenerate c.length) → Mono P.map)
  (a b : X.obj (op ⦋0⦌)) (A : Set (X.obj (op ⦋0⦌)))

/-- Each original reverse-inclusion arrow removes precisely the gates outside its target set. -/
def gateChainHomMap {S T : FlagGateIndex A R} (f : S ⟶ T) :
    gateListHom a b (gateIndexList R hrefl htrans hanti A S) ⟶
      gateListHom a b (gateIndexList R hrefl htrans hanti A T) :=
  gateListFilter (fun w ↦ decide (w ∈ T.val)) a b
    (gateIndexList R hrefl htrans hanti A S) ≫
      eqToHom (congrArg (gateListHom a b)
        (gateChainList_filter R hrefl htrans hanti T.property.2.1 T.property.2.2.2
          S.property.2.1 S.property.2.2.2 (leOfHom f)))

/-- The map attached to every original gate-set inclusion preserves original total composition. -/
theorem gateChainHomMap_comp {S T : FlagGateIndex A R} (f : S ⟶ T) :
    gateChainHomMap R hrefl htrans hanti a b A f ≫
      gateListComposition a b (gateIndexList R hrefl htrans hanti A T) =
        gateListComposition a b (gateIndexList R hrefl htrans hanti A S) := by
  dsimp only [gateChainHomMap, gateIndexList]
  rw [Category.assoc,
    gateListComposition_eqToHom a b
      (gateChainList_filter R hrefl htrans hanti T.property.2.1 T.property.2.2.2
        S.property.2.1 S.property.2.2.2 (leOfHom f)), gateListFilter_comp]

/-- The consecutive-original-Hom product diagram on the unchanged finite-chain-set index. -/
def gateChainHomDiagram : FlagGateIndex A R ⥤ SSet.{u} where
  obj S := gateListHom a b (gateIndexList R hrefl htrans hanti A S)
  map f := gateChainHomMap R hrefl htrans hanti a b A f
  map_id S := by
    let : Mono (gateListComposition a b (gateIndexList R hrefl htrans hanti A S)) :=
      gateChainComposition_mono R hrefl htrans hanti hbound hm a b A S
    apply (cancel_mono (gateListComposition a b _)).mp
    rw [gateChainHomMap_comp, Category.id_comp]
  map_comp {S T U} f g := by
    let : Mono (gateListComposition a b (gateIndexList R hrefl htrans hanti A U)) :=
      gateChainComposition_mono R hrefl htrans hanti hbound hm a b A U
    apply (cancel_mono (gateListComposition a b _)).mp
    rw [gateChainHomMap_comp, Category.assoc, gateChainHomMap_comp, gateChainHomMap_comp]

/-- The product diagram augments to the same original Hom by original iterated composition. -/
def gateChainHomCocone : Cocone (gateChainHomDiagram R hrefl htrans hanti hbound hm a b A) where
  pt := flagHom X a b
  ι := {
    app S := gateListComposition a b (gateIndexList R hrefl htrans hanti A S)
    naturality _ _ f := by
      exact (gateChainHomMap_comp R hrefl htrans hanti a b A f).trans
        (Category.comp_id _).symm }

/-- The pointwise decompositions form a natural isomorphism for every original inclusion arrow. -/
def gateChainDiagramIso : flagGateDiagram a b A R ≅
    gateChainHomDiagram R hrefl htrans hanti hbound hm a b A :=
  NatIso.ofComponents (gateChainHomIso R hrefl htrans hanti hbound hm a b A) (by
    intro S T f
    let : Mono (gateListComposition a b (gateIndexList R hrefl htrans hanti A T)) :=
      gateChainComposition_mono R hrefl htrans hanti hbound hm a b A T
    apply (cancel_mono (gateListComposition a b _)).mp
    change (flagGateDiagram a b A R).map f ≫
        (gateChainHomIso R hrefl htrans hanti hbound hm a b A T).hom ≫ _ =
      ((gateChainHomIso R hrefl htrans hanti hbound hm a b A S).hom ≫
        gateChainHomMap R hrefl htrans hanti a b A f) ≫ _
    rw [gateChainHomIso_hom_comp, Category.assoc, gateChainHomMap_comp,
      gateChainHomIso_hom_comp]
    exact Subfunctor.homOfLe_ι (flagGateSubcomplex_antitone a b (leOfHom f)))

/-- The assembled diagram isomorphism retains the original augmentation at every index object. -/
theorem gateChainDiagramIso_augmentation (S : FlagGateIndex A R) :
    (gateChainDiagramIso R hrefl htrans hanti hbound hm a b A).hom.app S ≫
      (gateChainHomCocone R hrefl htrans hanti hbound hm a b A).ι.app S =
        (flagGateCocone a b A R).ι.app S :=
  gateChainHomIso_hom_comp R hrefl htrans hanti hbound hm a b A S

/-- The literal binary necklace product discharges every generic order and support premise. -/
def productCutGateChainDiagramIso (n : ℕ) (factor : Fin n → NecklaceCode) (T : NecklaceCode)
    (a b : (productSpace.{u} n factor ⨯ T.toSSet).obj (op ⦋0⦌))
    (A : Set ((productSpace n factor ⨯ T.toSSet).obj (op ⦋0⦌))) :=
  gateChainDiagramIso (productCutVertexLE n factor T) (productCutVertexLE_refl n factor T)
    (productCutVertexLE_trans n factor T) (productCutVertexLE_antisymm n factor T)
    (productCut_support_bounds n factor T) (productCut_necklace_mono_of_nondegenerate n factor T)
    a b A

end

end DaggerOriginalProductGadget
