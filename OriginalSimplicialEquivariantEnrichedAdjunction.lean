import OriginalSimplicialEquivariantParameterTensor
import TopCatModelCategory.SSet.StandardSimplex

/-!
# The original simplicial equivariant tensor-enriched-map adjunction

For arbitrary original C₂-simplicial actions, every enriched mapping degree is an actual
 equivariant map from the ordinary parameter product. Arbitrary simplicial parameters are
 represented by these degrees using native Yoneda, not just standard simplices or vertices.
 The actual tensor and enriched mapping functors are adjoint. The original enriched singular
 mapping construction is the exact specialization to the native singular action.
-/

set_option autoImplicit false

open CategoryTheory MonoidalCategory Opposite Simplicial DaggerModels
open DaggerOriginalDaggerRealizationC2Action DaggerOriginalSimplicialEquivariantParameterTensor

universe u

namespace DaggerOriginalSimplicialEquivariantEnrichedAdjunction

noncomputable section

/-- The literal enriched mapping simplicial set for arbitrary original target actions. -/
def enrichedMapping (E B : Action SSet.{u} C2.{u}) : SSet.{u} where
  obj n := simplicialParameterTensor E (SSet.stdSimplex.obj n.unop) ⟶ B
  map i q := simplicialParameterTensorMap E (SSet.stdSimplex.map i.unop) ≫ q
  map_id n := by
    funext q
    change simplicialParameterTensorMap E (SSet.stdSimplex.map (𝟙 n.unop)) ≫ q = q
    rw [CategoryTheory.Functor.map_id SSet.stdSimplex n.unop,
      simplicialParameterTensorMap_id, Category.id_comp]
  map_comp i j := by
    funext q
    simp only [unop_comp, Functor.map_comp, simplicialParameterTensorMap_comp, Category.assoc]
    rfl

/-- Actual equivariant target maps act by literal postcomposition in each degree. -/
def enrichedMappingMap (E : Action SSet.{u} C2.{u}) {B C : Action SSet.{u} C2.{u}} (f : B ⟶ C) :
    enrichedMapping E B ⟶ enrichedMapping E C where
  app n q := q ≫ f
  naturality n m i := by
    funext q
    change (simplicialParameterTensorMap E (SSet.stdSimplex.map i.unop) ≫ q) ≫ f =
      simplicialParameterTensorMap E (SSet.stdSimplex.map i.unop) ≫ (q ≫ f)
    exact Category.assoc _ _ _

/-- The enriched mapping functor retains every original equivariant target and target map. -/
def enrichedMappingFunctor (E : Action SSet.{u} C2.{u}) : Action SSet.{u} C2.{u} ⥤ SSet.{u} where
  obj := enrichedMapping E
  map := enrichedMappingMap E
  map_id B := by ext n q; exact Category.comp_id q
  map_comp f g := by ext n q; exact (Category.assoc q f g).symm

/-- The ordinary product tensor functor uses the original action on its first factor only. -/
def parameterTensorFunctor (E : Action SSet.{u} C2.{u}) : SSet.{u} ⥤ Action SSet.{u} C2.{u} where
  obj := simplicialParameterTensor E
  map := simplicialParameterTensorMap E
  map_id := simplicialParameterTensorMap_id E
  map_comp := simplicialParameterTensorMap_comp E

/-- An equivariant map on an arbitrary parameter gives its actual Yoneda families. -/
def enrichedCurry (E B : Action SSet.{u} C2.{u}) (A : SSet.{u})
    (q : simplicialParameterTensor E A ⟶ B) : A ⟶ enrichedMapping E B where
  app n a := simplicialParameterTensorMap E (SSet.yonedaEquiv.symm a) ≫ q
  naturality n m i := by
    funext a
    change simplicialParameterTensorMap E (SSet.yonedaEquiv.symm (A.map i a)) ≫ q =
      simplicialParameterTensorMap E (SSet.stdSimplex.map i.unop) ≫
        (simplicialParameterTensorMap E (SSet.yonedaEquiv.symm a) ≫ q)
    have h : SSet.yonedaEquiv.symm (A.map i a) =
        SSet.stdSimplex.map i.unop ≫ SSet.yonedaEquiv.symm a :=
      SSet.yonedaEquiv_symm_map i.unop a
    rw [h, simplicialParameterTensorMap_comp, Category.assoc]

/-- Evaluation on the identity simplex recovers the actual equivariant parameter map. -/
def enrichedUncurry (E B : Action SSet.{u} C2.{u}) (A : SSet.{u})
    (q : A ⟶ enrichedMapping E B) : simplicialParameterTensor E A ⟶ B where
  hom :=
    { app n p := (q.app n p.2).hom.app n
        (p.1, SSet.stdSimplex.objEquiv.symm (𝟙 n.unop))
      naturality n m i := by
        funext p
        have hq := congrFun (q.naturality i) p.2
        change q.app m (A.map i p.2) =
          simplicialParameterTensorMap E (SSet.stdSimplex.map i.unop) ≫ q.app n p.2 at hq
        change (q.app m (A.map i p.2)).hom.app m
            (E.V.map i p.1, SSet.stdSimplex.objEquiv.symm (𝟙 m.unop)) =
          B.V.map i ((q.app n p.2).hom.app n
            (p.1, SSet.stdSimplex.objEquiv.symm (𝟙 n.unop)))
        rw [hq]
        have hn := congrFun ((q.app n p.2).hom.naturality i)
          (p.1, SSet.stdSimplex.objEquiv.symm (𝟙 n.unop))
        simpa [simplicialParameterTensorMap, SSet.stdSimplex.map_apply,
          Category.id_comp, Category.comp_id] using hn }
  comm g := by
    ext n ⟨e, a⟩
    exact congrFun (NatTrans.congr_app ((q.app n a).comm g) n)
      (e, SSet.stdSimplex.objEquiv.symm (𝟙 n.unop))

/-- Identity-simplex evaluation inverts the original Yoneda-family construction. -/
theorem enrichedUncurry_curry (E B : Action SSet.{u} C2.{u}) (A : SSet.{u})
    (q : simplicialParameterTensor E A ⟶ B) :
    enrichedUncurry E B A (enrichedCurry E B A q) = q := by
  ext n ⟨e, a⟩
  change q.hom.app n (e, (SSet.yonedaEquiv.symm a).app n
    (SSet.yonedaEquiv (𝟙 (SSet.stdSimplex.obj n.unop)))) = q.hom.app n (e, a)
  have h : (SSet.yonedaEquiv.symm a).app n
      (SSet.yonedaEquiv (𝟙 (SSet.stdSimplex.obj n.unop))) = a :=
    (SSet.yonedaEquiv (X := A) (n := n.unop)).apply_symm_apply a
  rw [h]

/-- The full family is recovered in every degree, including every simplex of each parameter. -/
theorem enrichedCurry_uncurry (E B : Action SSet.{u} C2.{u}) (A : SSet.{u})
    (q : A ⟶ enrichedMapping E B) :
    enrichedCurry E B A (enrichedUncurry E B A q) = q := by
  apply NatTrans.ext
  funext n a
  apply Action.Hom.ext
  apply NatTrans.ext
  funext m p
  rcases p with ⟨e, t⟩
  have hq := congrFun (q.naturality (SSet.stdSimplex.objEquiv t).op) a
  change q.app m (A.map (SSet.stdSimplex.objEquiv t).op a) =
    simplicialParameterTensorMap E (SSet.stdSimplex.map (SSet.stdSimplex.objEquiv t)) ≫
      q.app n a at hq
  change (q.app m (A.map (SSet.stdSimplex.objEquiv t).op a)).hom.app m
      (e, SSet.stdSimplex.objEquiv.symm (𝟙 m.unop)) = (q.app n a).hom.app m (e, t)
  rw [hq]
  change (q.app n a).hom.app m
      (e, SSet.stdSimplex.objEquiv.symm (𝟙 m.unop ≫ SSet.stdSimplex.objEquiv t)) = _
  rw [Category.id_comp, Equiv.symm_apply_apply]

/-- Arbitrary parameter homs are represented by the literal equivariant enriched mapping object.
-/
def enrichedHomEquiv (E B : Action SSet.{u} C2.{u}) (A : SSet.{u}) :
    (simplicialParameterTensor E A ⟶ B) ≃ (A ⟶ enrichedMapping E B) where
  toFun := enrichedCurry E B A
  invFun := enrichedUncurry E B A
  left_inv := enrichedUncurry_curry E B A
  right_inv := enrichedCurry_uncurry E B A

/-- Every original parameter map commutes with the actual enriched hom correspondence. -/
theorem enrichedHomEquiv_parameter_naturality (E B : Action SSet.{u} C2.{u})
    {A A' : SSet.{u}} (i : A ⟶ A') (q : simplicialParameterTensor E A' ⟶ B) :
    enrichedHomEquiv E B A (simplicialParameterTensorMap E i ≫ q) =
      i ≫ enrichedHomEquiv E B A' q := by
  ext n a
  change simplicialParameterTensorMap E (SSet.yonedaEquiv.symm a) ≫
      (simplicialParameterTensorMap E i ≫ q) =
    simplicialParameterTensorMap E (SSet.yonedaEquiv.symm (i.app n a)) ≫ q
  rw [← SSet.yonedaEquiv_symm_comp, simplicialParameterTensorMap_comp, Category.assoc]

/-- Every original equivariant target map commutes with the actual hom correspondence. -/
theorem enrichedHomEquiv_target_naturality (E : Action SSet.{u} C2.{u}) (A : SSet.{u})
    {B C : Action SSet.{u} C2.{u}} (q : simplicialParameterTensor E A ⟶ B) (f : B ⟶ C) :
    enrichedHomEquiv E C A (q ≫ f) =
      enrichedHomEquiv E B A q ≫ enrichedMappingMap E f := by
  ext n a
  exact (Category.assoc _ _ _).symm

/-- The actual original ordinary equivariant tensor is left adjoint to the enriched Map functor.
-/
def enrichedAdjunction (E : Action SSet.{u} C2.{u}) :
    parameterTensorFunctor E ⊣ enrichedMappingFunctor E :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun A B ↦ enrichedHomEquiv E B A
      homEquiv_naturality_left_symm := by
        intro A A' B i q
        apply (enrichedHomEquiv E B A).injective
        change (enrichedHomEquiv E B A) ((enrichedHomEquiv E B A).symm (i ≫ q)) =
          enrichedHomEquiv E B A
            (simplicialParameterTensorMap E i ≫ (enrichedHomEquiv E B A').symm q)
        rw [Equiv.apply_symm_apply, enrichedHomEquiv_parameter_naturality,
          Equiv.apply_symm_apply]
      homEquiv_naturality_right := by
        intro A B C q f
        exact enrichedHomEquiv_target_naturality E A q f }

/-- The arbitrary-target Map is exactly the previous original enriched Sing construction. -/
theorem originalEnrichedSing_eq (X : ContAction TopCat.{u} C2.{u}) :
    enrichedMapping DaggerOriginalEC2SimplicialAction.simplicialAction (singularAction X) =
      originalEC2EnrichedSingMapping X := rfl

end

end DaggerOriginalSimplicialEquivariantEnrichedAdjunction
