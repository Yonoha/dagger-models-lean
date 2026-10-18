import OriginalGateSplitCocone

set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory Opposite Simplicial
open DaggerChosenRigidificationNecklace
open DaggerChosenRigidificationNecklace.NecklaceCode
open DaggerOriginalFlagFlankification

universe u

namespace DaggerOriginalProductGadget

noncomputable section

variable {X : SSet.{u}} {a v b : X.obj (op ⦋0⦌)} {q : SimplexCategoryᵒᵖ}

/-- The entire support of the original composition is the union of the two original supports. -/
theorem flagVertexSupport_comp (x : (flagHom X a v).obj q)
    (y : (flagHom X v b).obj q) :
    flagVertexSupport (flagCompApp x y) = flagVertexSupport x ∪ flagVertexSupport y := by
  induction x using Quot.ind with | _ p
  induction y using Quot.ind with | _ r
  change (fun z : Vertices.{u} (NecklaceCode.wedge p.1.code r.1.code) ↦
      vertexImage (NecklacesOver.wedge p.1 r.1) z.down) ''
    (mapVertices (wedgeιLeft p.1.code r.1.code) '' p.2.chain 0 ∪
      mapVertices (wedgeιRight p.1.code r.1.code) '' r.2.chain 0) = _
  rw [Set.image_union, Set.image_image, Set.image_image]
  congr 1
  · apply congrArg (fun f ↦ f '' p.2.chain 0)
    funext z
    change (NecklacesOver.wedge p.1 r.1).map.app _
      ((NecklaceCode.wedge p.1.code r.1.code).verticesEquiv.symm
        ((NecklaceCode.wedge p.1.code r.1.code).verticesEquiv
          ((wedgeιLeft p.1.code r.1.code).app _ (p.1.code.verticesEquiv.symm z)))) = _
    rw [Equiv.symm_apply_apply]
    exact congrFun (NatTrans.congr_app (NecklacesOver.wedge_left p.1 r.1) _) _
  · apply congrArg (fun f ↦ f '' r.2.chain 0)
    funext z
    change (NecklacesOver.wedge p.1 r.1).map.app _
      ((NecklaceCode.wedge p.1.code r.1.code).verticesEquiv.symm
        ((NecklaceCode.wedge p.1.code r.1.code).verticesEquiv
          ((wedgeιRight p.1.code r.1.code).app _ (r.1.code.verticesEquiv.symm z)))) = _
    rw [Equiv.symm_apply_apply]
    exact congrFun (NatTrans.congr_app (NecklacesOver.wedge_right p.1 r.1) _) _

variable (a v b)

/-- Original composition through v lands in the original subcomplex requiring v as a gate. -/
def gateComposition :
    flagHom X a v ⊗ flagHom X v b ⟶ (flagGateSubcomplex a b {v}).toFunctor where
  app q x := ⟨flagCompApp x.1 x.2, by
    change {v} ⊆ flagVertexSupport (flagCompApp x.1 x.2)
    rw [Set.singleton_subset_iff, flagVertexSupport_comp]
    exact Or.inl (flagVertexSupport_last x.1)⟩
  naturality p q α := by
    funext x
    apply Subtype.ext
    exact (flagCompApp_operator α x.1 x.2).symm

theorem gateComposition_ι :
    gateComposition a v b ≫ (flagGateSubcomplex a b {v}).ι = flagComposition X a v b := rfl

variable (hm : ∀ P : NecklacesOver X a b,
  (∀ c : P.code.Bead, beadElement P c ∈ X.nonDegenerate c.length) → Mono P.map)

/-- Split a simplex in the actual gate subcomplex using its established necklace-colimit model. -/
def gateSubcomplexSplit :
    (flagGateSubcomplex a b {v}).toFunctor ⟶ flagHom X a v ⊗ flagHom X v b :=
  (monicGateIso {v} hm).inv ≫ gateSplit a v b

/-- Split and then compose is the identity on the literal original gate subcomplex. -/
theorem gateSubcomplexSplit_recompose :
    gateSubcomplexSplit a v b hm ≫ gateComposition a v b =
      𝟙 (flagGateSubcomplex a b {v}).toFunctor := by
  apply (cancel_mono (flagGateSubcomplex a b {v}).ι).mp
  rw [Category.assoc, gateComposition_ι]
  change ((monicGateIso {v} hm).inv ≫ gateSplit a v b) ≫ flagComposition X a v b = _
  rw [Category.assoc, gateSplit_comp]
  change (monicGateIso {v} hm).inv ≫
    ((monicGateIso {v} hm).hom ≫ (flagGateSubcomplex a b {v}).ι) = _
  rw [Iso.inv_hom_id_assoc, Category.id_comp]

/-- The canonical split is injective; the converse roundtrip is a separate obligation. -/
theorem gateSubcomplexSplit_mono : Mono (gateSubcomplexSplit a v b hm) := by
  have h := gateSubcomplexSplit_recompose a v b hm
  exact mono_of_mono_fac h

include hm in
/-- Every gate simplex is an original composite through that same gate. -/
theorem gateComposition_epi : Epi (gateComposition a v b) := by
  have h := gateSubcomplexSplit_recompose a v b hm
  exact epi_of_epi_fac h

/-- The actual binary necklace product supplies the required monomorphism theorem. -/
def productCutGateSplit (n : ℕ) (factor : Fin n → NecklaceCode) (T : NecklaceCode)
    (a v b : (productSpace.{u} n factor ⨯ T.toSSet).obj (op ⦋0⦌)) :
    (flagGateSubcomplex a b {v}).toFunctor ⟶
      flagHom (productSpace n factor ⨯ T.toSSet) a v ⊗
        flagHom (productSpace n factor ⨯ T.toSSet) v b :=
  gateSubcomplexSplit a v b (productCut_necklace_mono_of_nondegenerate n factor T)

/-- No extra ordered-target premise remains in the product split/recomposition identity. -/
theorem productCutGateSplit_recompose (n : ℕ) (factor : Fin n → NecklaceCode)
    (T : NecklaceCode) (a v b : (productSpace.{u} n factor ⨯ T.toSSet).obj (op ⦋0⦌)) :
    productCutGateSplit n factor T a v b ≫ gateComposition a v b =
      𝟙 (flagGateSubcomplex a b {v}).toFunctor :=
  gateSubcomplexSplit_recompose a v b (productCut_necklace_mono_of_nondegenerate n factor T)

end

end DaggerOriginalProductGadget
