import ActualFibrantGadgetRigidificationWeak
import ActualCoherentNerveCoreComparisonWeak
import ActualFibrantGadgetExtensions
import OriginalEnrichedHomTransport

/-! The ORIGINAL first comparison is locally weak iff the ORIGINAL rigidified core unit is.
This equivalence retains arbitrary original quasi-categories; neither side is assumed true. -/
set_option autoImplicit false
open CategoryTheory HomotopicalAlgebra DaggerModels OrdinaryRigidification
open DaggerActualSimplicialIsomorphismComponentPart
open DaggerActualOrdinaryCoreIsomorphismComparison
open DaggerOriginalOrdinaryKanCoreSubcomplex DaggerOriginalEnrichedHomTransport
open DaggerActualDaggerOrdinaryCore
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerActualFirstCoreComparisonWeakReduction
noncomputable section

theorem post_hom_weak_iff {A B C : SimplicialCat.{u, u}} (F : A ⟶ B) (G : B ⟶ C)
    (hG : ∀ x y : B.Obj, WeakEquivalence (G.map x y)) (a b : A.Obj) :
    WeakEquivalence (F.map a b) ↔ WeakEquivalence ((F ≫ G).map a b) := by
  have := hG (F.obj a) (F.obj b)
  change WeakEquivalence (F.map a b) ↔
    WeakEquivalence (F.map a b ≫ G.map (F.obj a) (F.obj b))
  constructor
  · intro h
    have := h
    infer_instance
  · intro h
    have := h
    exact weakEquivalence_of_postcomp (F.map a b) (G.map (F.obj a) (F.obj b))

theorem hom_weak_congr {A B : SimplicialCat.{u, u}} {F G : A ⟶ B} (h : F = G)
    (a b : A.Obj) : WeakEquivalence (F.map a b) ↔ WeakEquivalence (G.map a b) :=
  (DaggerSSetGluing.weakEquivalence_iff_GW _).trans
    ((GW_functorHom_congr h a b).trans (DaggerSSetGluing.weakEquivalence_iff_GW _).symm)

theorem hom_weak_iff (X : SSet.{u}) [X.Quasicategory]
    (a b : (rigidification.obj (ordinaryCoreCandidate X : SSet.{u})).Obj) :
    WeakEquivalence ((comparison X).map a b) ↔
      WeakEquivalence ((rigidification.map
        (ordinaryCoreCandidateMap (DaggerActualFibrantGadgetData.unit.app X))).map a b) := by
  have := DaggerActualFibrantGadgetExtensions.gadget_quasicategory X
  let F := rigidification.map (DaggerActualFibrantGadgetData.unit.app X)
  let P := DaggerActualSimplicialIsomorphismComponentMaps.map F
  let G := rigidification.map
    (ordinaryCoreCandidateMap (DaggerActualFibrantGadgetData.unit.app X))
  let Q := comparison (DaggerActualFibrantGadgetData.gadget.obj X)
  have hP (x y : (part (rigidification.obj X)).Obj) : WeakEquivalence (P.map x y) :=
    DaggerActualIsomorphismPartLocalWeakInvariance.hom_weak F
      (DaggerActualFibrantGadgetRigidificationWeak.hom_weak X) x y
  have hQ (x y : (rigidification.obj (ordinaryCoreCandidate
      (DaggerActualFibrantGadgetData.gadget.obj X) : SSet.{u})).Obj) :
      WeakEquivalence (Q.map x y) :=
    DaggerActualCoherentNerveCoreComparisonWeak.hom_weak
      (OriginalOrdinaryLocalKanReplacement.replacement.obj (rigidification.obj X))
      (OriginalOrdinaryLocalKanReplacement.replacement_locallyKan _) x y
  have hs : comparison X ≫ P = G ≫ Q :=
    naturality (X := X) (Y := DaggerActualFibrantGadgetData.gadget.obj X)
      (DaggerActualFibrantGadgetData.unit.app X)
  exact (post_hom_weak_iff (comparison X) P hP a b).trans
    ((hom_weak_congr hs a b).trans (post_hom_weak_iff G Q hQ a b).symm)

theorem dagger_hom_weak_iff (X : DaggerSSet.{u}) [X.toSSet.Quasicategory]
    (a b : (DaggerRigidification.obj (coreDagger X)).Obj) :
    WeakEquivalence
        ((DaggerActualDaggerCoreIsomorphismComponentComparison.comparison X).map a b) ↔
      WeakEquivalence ((rigidification.map
        (ordinaryCoreCandidateMap (DaggerActualFibrantGadgetData.unit.app X.toSSet))).map a b) := by
  exact (hom_weak_congr (dagger_underlying X) a b).trans (hom_weak_iff X.toSSet a b)

end
end DaggerActualFirstCoreComparisonWeakReduction
