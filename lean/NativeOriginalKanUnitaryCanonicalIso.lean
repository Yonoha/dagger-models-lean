import NativeDaggerKanUnitaryCoreWeak

/-! For a Kan input, the ORIGINAL unitary core is the ORIGINAL canonical EC2 complex. -/
set_option autoImplicit false
open CategoryTheory Opposite Simplicial DaggerModels
open DaggerOriginalDaggerCoreCandidate DaggerOriginalUnitaryCoreConstruction
open DaggerOriginalUnitaryCoreCanonicalVertices DaggerOriginalEC2CanonicalVertexKan
open DaggerOriginalEC2CanonicalVertexSubcomplex DaggerOriginalEC2HomotopyFixedPointObject
open DaggerNativeKanRigHomWeakRecognition
universe u
namespace DaggerNativeOriginalKanUnitaryCanonicalIso
noncomputable section

/-- The inverse of the SAME underlying isomorphism also preserves the SAME original dagger. -/
def inverseOfUnderlying {X Y : DaggerSSet.{u}} (f : X ⟶ Y) [IsIso f.hom] : Y ⟶ X where
  hom := inv f.hom
  comm := by
    apply (cancel_epi f.hom).mp
    change f.hom ≫ (inv f.hom ≫ X.dagger) =
      f.hom ≫ (Y.dagger ≫ SSet.opFunctor.map (inv f.hom))
    simp only [← Category.assoc, IsIso.hom_inv_id, Category.id_comp]
    rw [f.comm, Category.assoc, ← SSet.opFunctor.map_comp, IsIso.hom_inv_id]
    rfl

def isoOfUnderlying {X Y : DaggerSSet.{u}} (f : X ⟶ Y) [IsIso f.hom] : X ≅ Y where
  hom := f
  inv := inverseOfUnderlying f
  hom_inv_id := by apply DaggerSSet.Hom.ext; exact IsIso.hom_inv_id f.hom
  inv_hom_id := by apply DaggerSSet.Hom.ext; exact IsIso.inv_hom_id f.hom

/-- The exact original greatest dagger core inclusion is an isomorphism for Kan inputs. -/
def coreIso (X : DaggerSSet.{u}) [X.toSSet.KanComplex] : daggerCoreCandidate X ≅ X := by
  have : IsIso (daggerCoreInclusion X).hom := core_inclusion_isIso X.toSSet
  exact isoOfUnderlying (daggerCoreInclusion X)

/-- The ORIGINAL U, with its ORIGINAL greatest core, maps isomorphically to the OLD complex. -/
def unitaryCanonicalIso (X : DaggerSSet.{u}) [X.toSSet.KanComplex] :
    unitaryCore X ≅ canonicalVertexFunctor.obj X :=
  canonicalVertexFunctor.mapIso (coreIso X)

theorem unitaryCanonicalIso_hom (X : DaggerSSet.{u}) [X.toSSet.KanComplex] :
    (unitaryCanonicalIso X).hom = canonicalVertexMap (daggerCoreInclusion X) := rfl

/-- The same original vertex label is retained by this exact original U isomorphism. -/
theorem unitaryCanonicalIso_vertex (X : DaggerSSet.{u}) [X.toSSet.KanComplex]
    (x : X.toSSet _⦋0⦌) :
    (((unitaryCanonicalIso X).hom).app (op ⦋0⦌) (canonicalUnitaryVertex X x)).val =
      canonicalZeroSimplex X x := by
  change (DaggerOriginalEC2HomotopyFixedPointFunctor.daggerHomotopyFixedPointFunctor.map
    (daggerCoreInclusion X)).app (op ⦋0⦌)
      (canonicalZeroSimplex (daggerCoreCandidate X) ((coreVertexEquiv X).symm x)) = _
  exact canonicalZeroSimplex_naturality (daggerCoreInclusion X) ((coreVertexEquiv X).symm x)

end
end DaggerNativeOriginalKanUnitaryCanonicalIso
