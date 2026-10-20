import OriginalSimplicialPiZeroFunctor
import OriginalAmbientDaggerPiZeroGroupoid

/-!
# Actual component equivalences of original fixed-object weak equivalences

Every ordinary original fixed-object functor induces the exact general native
component functor. The object map is the identity, giving essential surjectivity.
Homwise weak equivalences give full faithfulness by the native component theorem.
For the actual ambient dagger weak class, the original all-Hom characterization
supplies the hypothesis. The resulting equivalence retains the actual pi0 functor.
-/
set_option autoImplicit false
open CategoryTheory HomotopicalAlgebra DaggerModels
open DaggerOriginalFixedObjectSimplicialCategories DaggerOriginalFixedObjectDaggerCategories
open DaggerOriginalFixedObjectAmbientDaggerModel DaggerOriginalFixedObjectGroupoidTerminals
open DaggerOriginalSimplicialPiZeroCategory DaggerOriginalSimplicialPiZeroFunctor
open scoped SSet.modelCategoryQuillen DaggerOriginalFixedObjectAmbientDaggerModel
universe u
namespace DaggerOriginalFixedObjectPiZeroEquivalence
noncomputable section

/-- The exact component functor of the actual original identity-object-function map. -/
def fixedComponentFunctor {O : Type u} {C D : FixedSimplicialCategory O} (F : C ⟶ D) :
    componentObjects (original O C) ⥤ componentObjects (original O D) :=
  componentFunctor (originalHom F)

/-- All original fixed objects occur in the actual component functor's image. -/
def fixedComponentFunctorEssSurj {O : Type u} {C D : FixedSimplicialCategory O} (F : C ⟶ D) :
    (fixedComponentFunctor F).EssSurj :=
  ⟨fun y ↦ ⟨y, ⟨Iso.refl y⟩⟩⟩

/-- The original Homwise weak class induces the exact ordinary component equivalence. -/
theorem fixedComponentFunctorIsEquivalence {O : Type u} {C D : FixedSimplicialCategory O}
    (F : C ⟶ D) (hF : ∀ x y : O, WeakEquivalence (F.map x y)) :
    (fixedComponentFunctor F).IsEquivalence := by
  let h := componentFunctorFullyFaithful (originalHom F) hF
  exact ⟨h.faithful, h.full, fixedComponentFunctorEssSurj F⟩

/-- The actual ambient dagger weak class gives equivalence of the actual component categories. -/
theorem ambientComponentFunctorIsEquivalence {O : Type u} {H K : FixedDaggerCategory O}
    (f : H ⟶ K) [WeakEquivalence f] :
    (fixedComponentFunctor f.underlying).IsEquivalence :=
  fixedComponentFunctorIsEquivalence f.underlying
    ((weakEquivalence_iff_original f).1 inferInstance)

/-- A weak original interval augmentation supplies an actual native pi0 category equivalence. -/
def intervalComponentEquivalence {O : Type u} {H : FixedDaggerCategory O}
    (f : H ⟶ terminalFixedDagger O) [WeakEquivalence f] :
    componentObjects (original O H.underlying) ≌
      componentObjects (original O (terminalFixedDagger O).underlying) := by
  have := ambientComponentFunctorIsEquivalence f
  exact (fixedComponentFunctor f.underlying).asEquivalence

/-- The chosen equivalence's functor is exactly the original component augmentation. -/
theorem intervalComponentEquivalence_functor {O : Type u} {H : FixedDaggerCategory O}
    (f : H ⟶ terminalFixedDagger O) [WeakEquivalence f] :
    (intervalComponentEquivalence f).functor = fixedComponentFunctor f.underlying := rfl

end
end DaggerOriginalFixedObjectPiZeroEquivalence
