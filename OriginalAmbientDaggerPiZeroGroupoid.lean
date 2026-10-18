import OriginalSimplicialPiZeroCategory
import OriginalAmbientIntervalPiZeroDaggerInverse
import OriginalAmbientDaggerForgetCofibrancy
import OriginalCategoryWithPrescribedInverseChallengeProof

/-!
# Actual pi0 groupoid input for the original ambient dagger interval

Use the general component category retaining the original component Hom sets,
identities and composition. For a Homwise weak interval augmentation, the
original dagger map is an inverse on every component class. Both inverse laws
follow from the proved actual vertex laws and native component surjectivity.
Together with the proved ordinary cofibrancy this supplies the two DK80 input
conditions, without proving or assuming the localization-unit conclusion.
-/
set_option autoImplicit false
open CategoryTheory MonoidalCategory HomotopicalAlgebra Opposite Simplicial DaggerModels
open DaggerOriginalFixedObjectSimplicialCategories DaggerOriginalFixedObjectDaggerCategories
open DaggerOriginalFixedObjectGroupoidTerminals DaggerOriginalSimplicialPiZeroCategory
open DaggerOriginalAmbientIntervalPiZeroDaggerInverse DaggerOriginalAmbientDaggerForgetCofibrancy
open scoped SSet.modelCategoryQuillen DaggerOriginalFixedObjectAmbientDaggerModel
  DaggerOriginalAmbientDaggerForgetCofibrancy
universe u
namespace DaggerOriginalAmbientDaggerPiZeroGroupoid
noncomputable section

/-- The original dagger induces the unchanged native component map in the reverse Hom. -/
def componentDagger {O : Type u} (H : FixedDaggerCategory O)
    {x y : componentObjects (original O H.underlying)} (a : x ⟶ y) : y ⟶ x :=
  SSet.mapπ₀ (H.dagger.dagger x y) a

/-- On each vertex the component dagger is its actual original dagger class. -/
theorem componentDagger_mk {O : Type u} (H : FixedDaggerCategory O)
    {x y : componentObjects (original O H.underlying)}
    (a : (H.underlying.enriched.Hom x y).obj (op ⦋0⦌)) :
    componentDagger H (SSet.π₀.mk a : x ⟶ y) =
      (SSet.π₀.mk ((H.dagger.dagger x y).app (op ⦋0⦌) a) : y ⟶ x) := rfl

/-- The original dagger is an inverse on the left for every actual component class. -/
theorem componentDagger_inv_comp {O : Type u} {H : FixedDaggerCategory O}
    (f : H ⟶ terminalFixedDagger O) [WeakEquivalence f]
    {x y : componentObjects (original O H.underlying)} (a : x ⟶ y) :
    componentDagger H a ≫ a = 𝟙 y := by
  obtain ⟨a, rfl⟩ := SSet.π₀.mk_surjective a
  exact (vertexDagger_inverse_components f x y a).2

/-- The original dagger is an inverse on the right for every actual component class. -/
theorem componentDagger_comp_inv {O : Type u} {H : FixedDaggerCategory O}
    (f : H ⟶ terminalFixedDagger O) [WeakEquivalence f]
    {x y : componentObjects (original O H.underlying)} (a : x ⟶ y) :
    a ≫ componentDagger H a = 𝟙 x := by
  obtain ⟨a, rfl⟩ := SSet.π₀.mk_surjective a
  exact (vertexDagger_inverse_components f x y a).1

/-- The actual original component category is a groupoid with its original dagger inverse. -/
def intervalComponentGroupoid {O : Type u} {H : FixedDaggerCategory O}
    (f : H ⟶ terminalFixedDagger O) [WeakEquivalence f] :
    Groupoid.{u, u} (componentObjects (original O H.underlying)) :=
  DaggerOriginalCategoryWithPrescribedInverseChallengeProof.makeGroupoid
    (componentObjects (original O H.underlying)) (componentDagger H)
    (componentDagger_inv_comp f) (componentDagger_comp_inv f)

/-- The groupoid keeps the actual transported category, including all original composition. -/
theorem intervalComponentGroupoid_category {O : Type u} {H : FixedDaggerCategory O}
    (f : H ⟶ terminalFixedDagger O) [WeakEquivalence f] :
    (intervalComponentGroupoid f).toCategory = componentCategory (original O H.underlying) := rfl

/-- The groupoid uses exactly the original component dagger as its inverse. -/
theorem intervalComponentGroupoid_inverse {O : Type u} {H : FixedDaggerCategory O}
    (f : H ⟶ terminalFixedDagger O) [WeakEquivalence f]
    {x y : componentObjects (original O H.underlying)} (a : x ⟶ y) :
    @Groupoid.inv _ (intervalComponentGroupoid f) x y a = componentDagger H a := rfl

/-- Groupoid structure on precisely the actual transported component category. -/
def HasActualComponentGroupoid (C : SimplicialCat.{u, u}) : Prop :=
  ∃ G : Groupoid.{u, u} (componentObjects C), G.toCategory = componentCategory C

/-- The actual original weak interval has a groupoid structure on its unchanged pi0 category. -/
theorem interval_hasActualComponentGroupoid {O : Type u} {H : FixedDaggerCategory O}
    (f : H ⟶ terminalFixedDagger O) [WeakEquivalence f] :
    HasActualComponentGroupoid (original O H.underlying) :=
  ⟨intervalComponentGroupoid f, intervalComponentGroupoid_category f⟩

/-- Both DK80 inputs retain the exact ordinary lifting class and the actual pi0 category. -/
theorem ordinaryCofibrant_and_actualPiZeroGroupoid {O : Type u} {H : FixedDaggerCategory O}
    (f : H ⟶ terminalFixedDagger O) [IsCofibrant H] [WeakEquivalence f] :
    IsCofibrant H.underlying ∧ HasActualComponentGroupoid (original O H.underlying) :=
  ⟨forget_isCofibrant H, interval_hasActualComponentGroupoid f⟩

/-- The exact ordinary cofibrancy and actual pi0 groupoid inputs hold for every weak interval. -/
theorem ordinaryCofibrant_and_piZeroGroupoid {O : Type u} {H : FixedDaggerCategory O}
    (f : H ⟶ terminalFixedDagger O) [IsCofibrant H] [WeakEquivalence f] :
    IsCofibrant H.underlying ∧
      Nonempty (Groupoid.{u, u} (componentObjects (original O H.underlying))) :=
  ⟨forget_isCofibrant H, ⟨intervalComponentGroupoid f⟩⟩

end
end DaggerOriginalAmbientDaggerPiZeroGroupoid
