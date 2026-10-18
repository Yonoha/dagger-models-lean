import OriginalEC2SimplicialAction
import OriginalEC2HomotopyFixedPointFunctor

/-!
# Original simplicial equivariant parameter products and enriched mapping degrees

The original simplicial EC₂ is tensored with the actual standard simplex carrying the trivial
action. The enriched mapping degree is exactly the type of equivariant maps from this product.
All face and degeneracy maps are literal precomposition by the original parameter map.
-/

set_option autoImplicit false

open CategoryTheory MonoidalCategory Opposite Simplicial DaggerModels
open DaggerOriginalDaggerRealizationC2Action DaggerOriginalEC2SimplicialAction

universe u

namespace DaggerOriginalSimplicialEquivariantParameterTensor

noncomputable section

/-- The ordinary simplicial product, with the original action only on the first factor. -/
def simplicialParameterTensor (E : Action SSet.{u} C2.{u}) (A : SSet.{u}) :
    Action SSet.{u} C2.{u} where
  V := E.V ⊗ A
  ρ :=
    { toFun g := End.of ((E.ρ g).asHom ▷ A)
      map_one' := by
        apply End.ext
        apply NatTrans.ext
        funext n p
        exact Prod.ext
          (congrFun (NatTrans.congr_app (congrArg End.asHom E.ρ.map_one) n) p.1) rfl
      map_mul' g h := by
        apply End.ext
        apply NatTrans.ext
        funext n p
        exact Prod.ext
          (congrFun (NatTrans.congr_app (congrArg End.asHom (E.ρ.map_mul g h)) n) p.1) rfl }

/-- The actual parameter map acts on precisely the second simplicial factor. -/
def simplicialParameterTensorMap (E : Action SSet.{u} C2.{u}) {A B : SSet.{u}} (i : A ⟶ B) :
    simplicialParameterTensor E A ⟶ simplicialParameterTensor E B where
  hom := E.V ◁ i
  comm g := by
    ext n ⟨e, a⟩
    rfl

/-- The original identity parameter induces the identity product map. -/
theorem simplicialParameterTensorMap_id (E : Action SSet.{u} C2.{u}) (A : SSet.{u}) :
    simplicialParameterTensorMap E (𝟙 A) = 𝟙 (simplicialParameterTensor E A) := by
  ext n ⟨e, a⟩
  rfl

/-- Parameter composition is the same actual composition of equivariant product maps. -/
theorem simplicialParameterTensorMap_comp (E : Action SSet.{u} C2.{u})
    {A B C : SSet.{u}} (i : A ⟶ B) (j : B ⟶ C) :
    simplicialParameterTensorMap E (i ≫ j) =
      simplicialParameterTensorMap E i ≫ simplicialParameterTensorMap E j := by
  ext n ⟨e, a⟩
  rfl

/-- The literal singular action, using the native functor on actions. -/
def singularAction (X : ContAction TopCat.{u} C2.{u}) : Action SSet.{u} C2.{u} :=
  (TopCat.toSSet.mapAction C2.{u}).obj X.obj

/-- The singular action map is induced by the actual equivariant target map. -/
def singularActionMap {X Y : ContAction TopCat.{u} C2.{u}} (f : X ⟶ Y) :
    singularAction X ⟶ singularAction Y :=
  (TopCat.toSSet.mapAction C2.{u}).map f.hom

/-- The original enriched equivariant mapping simplicial set, with literal product-map degrees.
-/
def originalEC2EnrichedSingMapping (X : ContAction TopCat.{u} C2.{u}) : SSet.{u} where
  obj n := simplicialParameterTensor simplicialAction.{u} (SSet.stdSimplex.obj n.unop) ⟶
    singularAction X
  map i q := simplicialParameterTensorMap simplicialAction (SSet.stdSimplex.map i.unop) ≫ q
  map_id n := by
    funext q
    change simplicialParameterTensorMap simplicialAction (SSet.stdSimplex.map (𝟙 n.unop)) ≫ q = q
    have hi := CategoryTheory.Functor.map_id SSet.stdSimplex.{u} n.unop
    rw [hi, simplicialParameterTensorMap_id, Category.id_comp]
  map_comp i j := by
    funext q
    simp only [unop_comp, Functor.map_comp, simplicialParameterTensorMap_comp, Category.assoc]
    rfl

/-- The actual target map acts by postcomposition in every enriched mapping degree. -/
def originalEC2EnrichedSingMappingMap {X Y : ContAction TopCat.{u} C2.{u}} (f : X ⟶ Y) :
    originalEC2EnrichedSingMapping X ⟶ originalEC2EnrichedSingMapping Y where
  app n q := q ≫ singularActionMap f
  naturality m n i := by
    funext q
    change (simplicialParameterTensorMap simplicialAction (SSet.stdSimplex.map i.unop) ≫ q) ≫
        singularActionMap f =
      simplicialParameterTensorMap simplicialAction (SSet.stdSimplex.map i.unop) ≫
        (q ≫ singularActionMap f)
    exact Category.assoc _ _ _

end

end DaggerOriginalSimplicialEquivariantParameterTensor
