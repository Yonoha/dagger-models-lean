import DaggerModels.NerveOpposite
import DaggerModels.NerveVertices
import DaggerModels.SimplicialSet

/-!
# The actual dagger coherent nerve

The original nerve carries the original enriched dagger via the checked opposite
comparison. Full degree-zero enriched-functor extensionality proves fixed vertices.
The underlying simplicial set and every functor map are retained. This constructs
the right-hand functor of Part I `dj.lem.lift`, not its left adjoint or adjunction.
-/

open CategoryTheory Opposite
open scoped Simplicial

universe u

noncomputable section

namespace DaggerModels.OrdinaryRigidification.DaggerNerve

open NerveOpposite NerveVertices ThickeningReversal

/-- The existing enriched dagger with its actual ordinary opposite codomain. -/
def enrichedDagger (C : DaggerSimplicialCat.{u, u}) :
    C.toSimplicialCat ⟶ SimplicialCat.opposite C.toSimplicialCat :=
  DaggerSimplicialCat.daggerNatural.app C

/-- The actual enriched dagger satisfies the typed double-opposite involution. -/
theorem enrichedDagger_involutive (C : DaggerSimplicialCat.{u, u}) :
    enrichedDagger C ≫ SimplicialCat.oppositeFunctor.map (enrichedDagger C) ≫
      SimplicialCat.doubleOppositeHom C.toSimplicialCat = 𝟙 C.toSimplicialCat := by
  apply EnrichedFunctor.ext SSet
  case h_obj =>
    intro x
    rfl
  case h_map =>
    intro x y
    simpa [enrichedDagger, DaggerSimplicialCat.daggerNatural,
      DaggerSimplicialStructure.daggerFunctor, SimplicialCat.oppositeFunctor,
      SimplicialCat.oppositeMap, SimplicialCat.doubleOppositeHom, EnrichedFunctor.comp,
      EnrichedFunctor.id] using DaggerSimplicialStructure.dagger_involutive x y

/-- The existing dagger is natural for every actual dagger simplicial functor. -/
theorem enrichedDagger_naturality {C D : DaggerSimplicialCat.{u, u}} (F : C ⟶ D) :
    F.toEnrichedFunctor ≫ enrichedDagger D =
      enrichedDagger C ≫ SimplicialCat.oppositeFunctor.map F.toEnrichedFunctor :=
  DaggerSimplicialCat.daggerNatural.naturality F

/-- Apply the original nerve to dagger, then the actual opposite comparison. -/
def nerveDagger (C : DaggerSimplicialCat.{u, u}) :
    coherentNerve.obj C.toSimplicialCat ⟶ (coherentNerve.obj C.toSimplicialCat).op :=
  coherentNerve.map (enrichedDagger C) ≫ coherentNerveOppositeIso.hom.app C.toSimplicialCat

/-- The constructed simplicial dagger is involutive using the actual opposite coherence. -/
theorem nerveDagger_involutive (C : DaggerSimplicialCat.{u, u}) :
    nerveDagger C ≫ SSet.opFunctor.map (nerveDagger C) ≫
      SSet.opFunctorCompOpFunctorIso.hom.app (coherentNerve.obj C.toSimplicialCat) =
        𝟙 (coherentNerve.obj C.toSimplicialCat) := by
  have hn := coherentNerveOppositeIso.hom.naturality (enrichedDagger C)
  change coherentNerve.map (SimplicialCat.oppositeFunctor.map (enrichedDagger C)) ≫
      coherentNerveOppositeIso.hom.app (SimplicialCat.opposite C.toSimplicialCat) =
    coherentNerveOppositeIso.hom.app C.toSimplicialCat ≫
      SSet.opFunctor.map (coherentNerve.map (enrichedDagger C)) at hn
  unfold nerveDagger
  rw [Functor.map_comp]
  simp only [Category.assoc]
  rw [← reassoc_of% hn, coherentNerveOpposite_coherence]
  rw [← Functor.map_comp, ← Functor.map_comp]
  change coherentNerve.map (enrichedDagger C ≫
    SimplicialCat.oppositeFunctor.map (enrichedDagger C) ≫
      SimplicialCat.doubleOppositeHom C.toSimplicialCat) = _
  rw [enrichedDagger_involutive, CategoryTheory.Functor.map_id]

/-- Equality of complete enriched zero-simplices proves vertex fixing. -/
theorem nerveDagger_fixedVertices (C : DaggerSimplicialCat.{u, u})
    (P : (coherentNerve.obj C.toSimplicialCat).obj (op ⦋0⦌)) :
    SSet.opObjEquiv ((nerveDagger C).app (op ⦋0⦌) P) = P := by
  apply vertex_ext C.toSimplicialCat
  change P.down.obj (reverseObject ⦋0⦌ zeroObject) = P.down.obj zeroObject
  rw [zeroObject_eq (reverseObject ⦋0⦌ zeroObject)]

/-- The original coherent nerve equipped with the constructed strict vertex-fixing dagger. -/
def daggerCoherentNerveObj (C : DaggerSimplicialCat.{u, u}) : DaggerSSet.{u} where
  toSSet := coherentNerve.obj C.toSimplicialCat
  dagger := nerveDagger C
  involutive n P := congrFun (NatTrans.congr_app (nerveDagger_involutive C) (op ⦋n⦌)) P
  fixedVertices := nerveDagger_fixedVertices C

/-- The original coherent-nerve map commutes with the constructed daggers. -/
def daggerCoherentNerveMap {C D : DaggerSimplicialCat.{u, u}} (F : C ⟶ D) :
    daggerCoherentNerveObj C ⟶ daggerCoherentNerveObj D where
  hom := coherentNerve.map F.toEnrichedFunctor
  comm := by
    have hn := coherentNerveOppositeIso.hom.naturality F.toEnrichedFunctor
    change coherentNerve.map (SimplicialCat.oppositeFunctor.map F.toEnrichedFunctor) ≫
        coherentNerveOppositeIso.hom.app D.toSimplicialCat =
      coherentNerveOppositeIso.hom.app C.toSimplicialCat ≫
        SSet.opFunctor.map (coherentNerve.map F.toEnrichedFunctor) at hn
    change coherentNerve.map F.toEnrichedFunctor ≫
        (coherentNerve.map (enrichedDagger D) ≫
          coherentNerveOppositeIso.hom.app D.toSimplicialCat) =
      (coherentNerve.map (enrichedDagger C) ≫
          coherentNerveOppositeIso.hom.app C.toSimplicialCat) ≫
        SSet.opFunctor.map (coherentNerve.map F.toEnrichedFunctor)
    rw [← Category.assoc, ← Functor.map_comp, enrichedDagger_naturality,
      Functor.map_comp, Category.assoc]
    rw [hn, Category.assoc]

/-- The actual right-hand functor in Part I `dj.lem.lift`. -/
def daggerCoherentNerve : DaggerSimplicialCat.{u, u} ⥤ DaggerSSet.{u} where
  obj := daggerCoherentNerveObj
  map := daggerCoherentNerveMap
  map_id C := by
    apply DaggerSSet.Hom.ext
    exact coherentNerve.map_id C.toSimplicialCat
  map_comp F G := by
    apply DaggerSSet.Hom.ext
    exact coherentNerve.map_comp F.toEnrichedFunctor G.toEnrichedFunctor

/-- Forgetting the constructed dagger gives the exact existing ordinary nerve functor. -/
theorem daggerCoherentNerve_forget :
    daggerCoherentNerve.{u} ⋙ DaggerSSet.forget =
      DaggerSimplicialCat.forget ⋙ coherentNerve := rfl

end DaggerModels.OrdinaryRigidification.DaggerNerve
