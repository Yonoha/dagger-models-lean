import OriginalFixedObjectStrictDaggerCotensorRepresentation
import OriginalFixedObjectCotensorFibrations
import OriginalFixedObjectStrictDaggerModel
import OriginalContravariantCofibrantBrownChallengeProof

/-!
# Actual strict dagger mapping objects preserve cofibrant source weak equivalences

Transport whole lifting squares through the original cotensor equivalence.
Cotensor restriction into the genuine strict target is a fibration on all Hom
objects. Thus native mapping precomposition sends trivial cofibrations to
trivial fibrations. The independent contravariant Brown proof then handles weak
equivalences between cofibrant sources. No full simplicial-model axiom is assumed.
-/
set_option autoImplicit false
open CategoryTheory HomotopicalAlgebra Opposite
open DaggerOriginalFixedObjectDaggerCategories DaggerOriginalFixedObjectSimplicialCategories
open DaggerOriginalFixedObjectStrictGroupoidCotensors
open DaggerOriginalFixedObjectStrictDaggerCotensorRepresentation
open DaggerOriginalFixedObjectGroupoidInterval DaggerOriginalSimplicialCotensorRestriction
open scoped SSet.modelCategoryQuillen DaggerOriginalFixedObjectGroupoidClasses
  DaggerOriginalFixedObjectCofibrations DaggerOriginalFixedObjectStrictDaggerModel
universe u
namespace DaggerOriginalStrictDaggerMappingSourceInvariance
noncomputable section

/-- The exact strict cotensor restriction is fibrant on every original Hom. -/
theorem strictRestriction_fibration {O : Type u} {K L : SSet.{u}} (j : K ⟶ L) [Mono j]
    (D : FixedStrictDaggerGroupoids O) :
    Fibration (((strictDaggerCotensorBifunctor O).map j.op).app D) := by
  rw [DaggerOriginalFixedObjectGroupoidClasses.strictDagger_fibration_iff]
  intro x y
  have : (D.obj.underlying.enriched.Hom x y).KanComplex :=
    fixedStrictHom_kan ⟨D.obj.underlying, D.property⟩ x y
  exact pre_fibration j (D.obj.underlying.enriched.Hom x y)

/-- The cotensor correspondence carries the entire original native mapping lifting square. -/
theorem mappingSource_lifting {O : Type u} {K L : SSet.{u}} (j : K ⟶ L)
    {A B : FixedStrictDaggerGroupoids O} (i : A ⟶ B) (D : FixedStrictDaggerGroupoids O)
    [HasLiftingProperty i (((strictDaggerCotensorBifunctor O).map j.op).app D)] :
    HasLiftingProperty j (eHomWhiskerRight SSet i D) := by
  constructor
  intro f g sq
  let sq' : CommSq (strictCotensorHomEquiv A D L g) i
      (((strictDaggerCotensorBifunctor O).map j.op).app D)
      (strictCotensorHomEquiv B D K f) := by
    constructor
    rw [← strictCotensorHomEquiv_parameter, ← strictCotensorHomEquiv_source]
    exact congrArg (strictCotensorHomEquiv A D K) sq.w.symm
  let l := (strictCotensorHomEquiv B D L).symm sq'.lift
  refine ⟨⟨{ l := l, fac_left := ?_, fac_right := ?_ }⟩⟩
  · apply (strictCotensorHomEquiv B D K).injective
    rw [strictCotensorHomEquiv_parameter]
    change (strictCotensorHomEquiv B D L)
        ((strictCotensorHomEquiv B D L).symm sq'.lift) ≫ _ = _
    rw [Equiv.apply_symm_apply]
    exact sq'.fac_right
  · apply (strictCotensorHomEquiv A D L).injective
    rw [strictCotensorHomEquiv_source]
    change i ≫ (strictCotensorHomEquiv B D L)
        ((strictCotensorHomEquiv B D L).symm sq'.lift) = _
    rw [Equiv.apply_symm_apply]
    exact sq'.fac_left

/-- Actual native mapping precomposition takes trivial cofibrations to trivial fibrations. -/
theorem mappingSource_trivialFibration {O : Type u} {A B : FixedStrictDaggerGroupoids O}
    (i : A ⟶ B) [Cofibration i] [WeakEquivalence i] (D : FixedStrictDaggerGroupoids O) :
    trivialFibrations SSet.{u} (eHomWhiskerRight SSet i D) := by
  rw [← SSet.modelCategoryQuillen.rlp_I_eq_trivialFibrations]
  rintro _ _ _ ⟨n⟩
  have : Fibration
      (((strictDaggerCotensorBifunctor O).map (SSet.boundary n).ι.op).app D) :=
    strictRestriction_fibration (SSet.boundary n).ι D
  exact mappingSource_lifting (SSet.boundary n).ι i D

/-- The contravariant functor uses the full actual native enriched Hom and source maps. -/
def sourceMappingFunctor {O : Type u} (D : FixedStrictDaggerGroupoids O) :
    (FixedStrictDaggerGroupoids O)ᵒᵖ ⥤ SSet.{u} where
  obj A := A.unop ⟶[SSet] D
  map i := eHomWhiskerRight SSet i.unop D
  map_id A := eHomWhiskerRight_id SSet A.unop D
  map_comp i j := by
    change eHomWhiskerRight SSet (i ≫ j).unop D = _
    rw [unop_comp, eHomWhiskerRight_comp]

/-- Between actual cofibrant strict sources every native weak equivalence induces
a native weak equivalence on the entire mapping simplicial set. -/
theorem mappingSource_weakEquivalence {O : Type u} {A B : FixedStrictDaggerGroupoids O}
    (i : A ⟶ B) [IsCofibrant A] [IsCofibrant B] [WeakEquivalence i]
    (D : FixedStrictDaggerGroupoids O) : WeakEquivalence (eHomWhiskerRight SSet i D) := by
  exact DaggerOriginalContravariantCofibrantBrownChallengeProof.challengeProof
    (FixedStrictDaggerGroupoids O) SSet (sourceMappingFunctor D) (by
      intro X Y j hj hw
      have : Cofibration j := hj
      have : WeakEquivalence j := hw
      exact ((mem_trivialFibrations_iff _).1 (mappingSource_trivialFibration j D)).2)
    inferInstance inferInstance i inferInstance

end
end DaggerOriginalStrictDaggerMappingSourceInvariance
