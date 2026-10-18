import NativeKanRigHomWeakRecognition
import ActualLocallyKanGroupoidalCoherentNerve

/-!
# The original coherent nerve preserves these groupoidal local weak maps

Use the already proved original counit and Kan recognition theorem. This is the
coherent-nerve leg needed for the cotensor resolution, with every original object map.
-/
set_option autoImplicit false
open CategoryTheory Opposite Simplicial HomotopicalAlgebra DaggerModels OrdinaryRigidification
open DaggerOriginalAmbientDaggerPiZeroGroupoid
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerNativeGroupoidalCoherentNerveWeak
noncomputable section

/-- The actual coherent-nerve vertex is mapped by the original object function. -/
theorem vertex_map {C D : SimplicialCat.{u, u}} (F : C ⟶ D)
    (x : (coherentNerve.obj C).obj (op ⦋0⦌)) :
    NerveVertices.vertexEquiv D ((coherentNerve.map F).app (op ⦋0⦌) x) =
      F.obj (NerveVertices.vertexEquiv C x) := rfl

theorem vertices_surjective {C D : SimplicialCat.{u, u}} (F : C ⟶ D)
    (hF : Function.Surjective F.obj) :
    Function.Surjective ((coherentNerve.map F).app (op ⦋0⦌)) := by
  intro y
  obtain ⟨x, hx⟩ := hF (NerveVertices.vertexEquiv D y)
  refine ⟨(NerveVertices.vertexEquiv C).symm x, ?_⟩
  apply (NerveVertices.vertexEquiv D).injective
  rw [vertex_map, Equiv.apply_symm_apply, hx]

/-- Counit naturality retains the entire original functor, so two-out-of-three applies. -/
theorem rig_hom_weak {C D : SimplicialCat.{u, u}} (F : C ⟶ D)
    (hC : ∀ x y : C.Obj, SSet.KanComplex (C.enriched.Hom x y))
    (hD : ∀ x y : D.Obj, SSet.KanComplex (D.enriched.Hom x y))
    (hF : ∀ x y : C.Obj, WeakEquivalence (F.map x y))
    (a b : (rigidification.obj (coherentNerve.obj C)).Obj) :
    WeakEquivalence ((rigidification.map (coherentNerve.map F)).map a b) := by
  let R := rigidification.map (coherentNerve.map F)
  let eC := rigidificationCoherentNerveAdjunction.counit.app C
  let eD := rigidificationCoherentNerveAdjunction.counit.app D
  have : WeakEquivalence (eC.map a b) :=
    (DaggerSSetGluing.weakEquivalence_iff_GW _).2
      (DaggerActualRightConeRigidificationWeak.ordinary_counit_local C hC a b)
  have : WeakEquivalence (F.map (eC.obj a) (eC.obj b)) := hF _ _
  have hcomp : WeakEquivalence ((eC ≫ F).map a b) := by
    change WeakEquivalence (eC.map a b ≫ F.map (eC.obj a) (eC.obj b))
    infer_instance
  have hn : R ≫ eD = eC ≫ F :=
    rigidificationCoherentNerveAdjunction.counit.naturality F
  have : WeakEquivalence (R.map a b ≫ eD.map (R.obj a) (R.obj b)) := by
    change WeakEquivalence ((R ≫ eD).map a b)
    rw [hn]
    exact hcomp
  have : WeakEquivalence (eD.map (R.obj a) (R.obj b)) :=
    (DaggerSSetGluing.weakEquivalence_iff_GW _).2
      (DaggerActualRightConeRigidificationWeak.ordinary_counit_local D hD _ _)
  exact weakEquivalence_of_postcomp (R.map a b) (eD.map (R.obj a) (R.obj b))

/-- No extra change of nerve, objects or weak-equivalence class is made. -/
theorem map_weak {C D : SimplicialCat.{u, u}} (F : C ⟶ D)
    (hC : ∀ x y : C.Obj, SSet.KanComplex (C.enriched.Hom x y))
    (hD : ∀ x y : D.Obj, SSet.KanComplex (D.enriched.Hom x y))
    (hGC : HasActualComponentGroupoid C) (hGD : HasActualComponentGroupoid D)
    (hF : ∀ x y : C.Obj, WeakEquivalence (F.map x y))
    (hO : Function.Surjective F.obj) : WeakEquivalence (coherentNerve.map F) := by
  have := DaggerActualLocallyKanGroupoidalCoherentNerve.kan C hC hGC
  have := DaggerActualLocallyKanGroupoidalCoherentNerve.kan D hD hGD
  exact DaggerNativeKanRigHomWeakRecognition.weak_of_rig_hom_weak_and_vertices
    (coherentNerve.map F) (rig_hom_weak F hC hD hF) (vertices_surjective F hO)

end
end DaggerNativeGroupoidalCoherentNerveWeak
