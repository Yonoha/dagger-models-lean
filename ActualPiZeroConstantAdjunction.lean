import ActualPiZeroConstantHomEquivalence

/-! The original full component-category functor is left adjoint to constant enrichment. -/
set_option autoImplicit false
open CategoryTheory Opposite Simplicial DaggerModels
open DaggerUnitaryDiscrete DaggerActualConstantSimplicialCategory
open DaggerActualConstantEnrichmentFunctor DaggerActualPiZeroConstantHomEquivalence
open DaggerOriginalSimplicialPiZeroCategory DaggerOriginalSimplicialPiZeroFunctor
universe u
namespace DaggerActualPiZeroConstantAdjunction
noncomputable section

def bundledHomEquiv (C : SimplicialCat.{u, u}) (A : Cat.{u, u}) :
    (piZeroFunctor.obj C ⟶ A) ≃ (C ⟶ constantFunctor.obj A) where
  toFun F := fromOrdinary C A F.toFunctor
  invFun F := (toOrdinary C A F).toCatHom
  left_inv F := by
    apply Cat.Hom.ext
    exact to_from C A F.toFunctor
  right_inv F := from_to C A F

def piZeroConstantAdjunction : piZeroFunctor.{u} ⊣ constantFunctor :=
  Adjunction.mkOfHomEquiv
    { homEquiv := bundledHomEquiv
      homEquiv_naturality_left_symm := by
        intro C C' A F G
        letI := C.enriched
        letI := C'.enriched
        letI := (constant A).enriched
        change (toOrdinary C A (F ≫ G)).toCatHom =
          (componentFunctor F ⋙ toOrdinary C' A G).toCatHom
        apply Cat.Hom.ext
        refine CategoryTheory.Functor.hext (fun _ ↦ rfl) ?_
        intro x y a
        obtain ⟨v, rfl⟩ := SSet.π₀.mk_surjective a
        apply heq_of_eq
        change (constantHomEquiv _ _) ((F ≫ G).map x y) (SSet.π₀.mk v) =
          (constantHomEquiv _ _) (G.map (F.obj x) (F.obj y))
            (SSet.π₀.mk ((F.map x y).app (op ⦋0⦌) v))
        simp only [constantHomEquiv_mk]
        rfl
      homEquiv_naturality_right := by
        intro C A B F G
        letI := C.enriched
        letI := (constant A).enriched
        letI := (constant B).enriched
        change fromOrdinary C B (F.toFunctor ⋙ G.toFunctor) =
          fromOrdinary C A F.toFunctor ≫ constantMap G.toFunctor
        apply EnrichedFunctor.ext SSet (fun _ ↦ rfl)
        intro x y
        simp only [eqToHom_refl, Category.comp_id] }

end
end DaggerActualPiZeroConstantAdjunction
