import OriginalCoreLeftMappingFunctoriality

/-!
# Weak equivalences of the actual ordinary-core mapping spaces

The literal square of original mapping maps commutes on native pointed
homotopy classes. The two original-core mapping inclusions are bijective in
positive degrees. Thus an ambient mapping-space weak equivalence gives the
same positive comparisons for the core mapping map. Native full faithfulness
supplies the component comparison. Actual ambient mapping-space weak
equivalences for all endpoints therefore induce weak equivalences of all
actual original-core mapping spaces, without assuming that conclusion.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial HomotopicalAlgebra
open DaggerOriginalInnerHornFillers DaggerOriginalOrdinaryKanCoreSubcomplex
open DaggerOriginalOrdinaryKanCoreInnerHorns
open DaggerOriginalQuasicategoryLeftMappingSpace DaggerOriginalLeftMappingFunctoriality
open DaggerOriginalLeftMappingFullFaithfulness
open DaggerOriginalCoreLeftMappingFullComparison
open DaggerOriginalCoreLeftMappingHomotopyComparison DaggerOriginalCoreLeftMappingFunctoriality

universe u

namespace DaggerOriginalCoreLeftMappingWeakEquivalences

noncomputable section

/-- The actual original core/ambient mapping square commutes on the same pointed homotopy maps.
-/
theorem coreMappingMap_mapπ_square {X Y : SSet.{u}} (f : X ⟶ Y)
    (a b : (ordinaryCoreCandidate X : SSet.{u}).obj (op ⦋0⦌)) (n : ℕ)
    (v : (leftMappingSpace (ordinaryCoreCandidate X : SSet.{u}) a b).obj (op ⦋0⦌)) :
    SSet.KanComplex.mapπ (coreMappingInclusion Y
        ((ordinaryCoreCandidateMap f).app (op ⦋0⦌) a)
        ((ordinaryCoreCandidateMap f).app (op ⦋0⦌) b)) n
        ((coreMappingMap f a b).app (op ⦋0⦌) v)
        ((coreMappingInclusion Y
          ((ordinaryCoreCandidateMap f).app (op ⦋0⦌) a)
          ((ordinaryCoreCandidateMap f).app (op ⦋0⦌) b)).app (op ⦋0⦌)
            ((coreMappingMap f a b).app (op ⦋0⦌) v)) rfl ∘
      SSet.KanComplex.mapπ (coreMappingMap f a b) n v
        ((coreMappingMap f a b).app (op ⦋0⦌) v) rfl =
    SSet.KanComplex.mapπ (leftMappingMap f a.val b.val) n
        ((coreMappingInclusion X a b).app (op ⦋0⦌) v)
        ((coreMappingInclusion Y
          ((ordinaryCoreCandidateMap f).app (op ⦋0⦌) a)
          ((ordinaryCoreCandidateMap f).app (op ⦋0⦌) b)).app (op ⦋0⦌)
            ((coreMappingMap f a b).app (op ⦋0⦌) v)) rfl ∘
      SSet.KanComplex.mapπ (coreMappingInclusion X a b) n v
        ((coreMappingInclusion X a b).app (op ⦋0⦌) v) rfl := by
  rw [SSet.KanComplex.mapπ_comp_mapπ, SSet.KanComplex.mapπ_comp_mapπ]
  funext p
  obtain ⟨p, rfl⟩ := SSet.KanComplex.π.mk_surjective p
  simp only [SSet.KanComplex.mapπ_mk]
  apply congrArg SSet.KanComplex.π.mk
  apply SSet.Subcomplex.RelativeMorphism.ext
  change p.map ≫ (coreMappingMap f a b ≫ coreMappingInclusion Y
      ((ordinaryCoreCandidateMap f).app (op ⦋0⦌) a)
      ((ordinaryCoreCandidateMap f).app (op ⦋0⦌) b)) =
    p.map ≫ (coreMappingInclusion X a b ≫ leftMappingMap f a.val b.val)
  rw [coreMappingMap_comp_inclusion]

/-- An actual ambient mapping weak equivalence gives bijectivity on positive core mapping
 homotopy groups. -/
theorem coreMappingMap_mapπ_positive_bijective {X Y : SSet.{u}} (f : X ⟶ Y)
    (hX : innerHornFillers X) (hY : innerHornFillers Y)
    (a b : (ordinaryCoreCandidate X : SSet.{u}).obj (op ⦋0⦌))
    (hf : SSet.KanComplex.W (leftMappingMap f a.val b.val)) (n : ℕ)
    (v : (leftMappingSpace (ordinaryCoreCandidate X : SSet.{u}) a b).obj (op ⦋0⦌)) :
    Function.Bijective (SSet.KanComplex.mapπ (coreMappingMap f a b) (n + 1) v
      ((coreMappingMap f a b).app (op ⦋0⦌) v) rfl) := by
  let a' := (ordinaryCoreCandidateMap f).app (op ⦋0⦌) a
  let b' := (ordinaryCoreCandidateMap f).app (op ⦋0⦌) b
  let v' := (coreMappingMap f a b).app (op ⦋0⦌) v
  have htarget := coreMappingInclusion_mapπ_positive_bijective Y hY a' b' n v'
  have hsource := coreMappingInclusion_mapπ_positive_bijective X hX a b n v
  have hamb := hf.bijective (n + 1) ((coreMappingInclusion X a b).app (op ⦋0⦌) v)
    ((coreMappingInclusion Y a' b').app (op ⦋0⦌) v') rfl
  have hcomp := hamb.comp hsource
  rw [← coreMappingMap_mapπ_square f a b (n + 1) v] at hcomp
  constructor
  · intro p q hpq
    apply hcomp.1
    exact congrArg (SSet.KanComplex.mapπ (coreMappingInclusion Y a' b') (n + 1) v'
      ((coreMappingInclusion Y a' b').app (op ⦋0⦌) v') rfl) hpq
  · intro q
    obtain ⟨p, hp⟩ := hcomp.2
      (SSet.KanComplex.mapπ (coreMappingInclusion Y a' b') (n + 1) v'
        ((coreMappingInclusion Y a' b').app (op ⦋0⦌) v') rfl q)
    exact ⟨p, htarget.1 hp⟩

/-- Actual ambient mapping weak equivalences induce actual original-core mapping weak
 equivalences. -/
theorem coreMappingMap_weakEquivalence {X Y : SSet.{u}} (f : X ⟶ Y)
    (hX : innerHornFillers X) (hY : innerHornFillers Y)
    (hmap : ∀ x y : X.obj (op ⦋0⦌), WeakEquivalence (leftMappingMap f x y))
    (a b : (ordinaryCoreCandidate X : SSet.{u}).obj (op ⦋0⦌)) :
    WeakEquivalence (coreMappingMap f a b) := by
  have hCX : innerHornFillers (ordinaryCoreCandidate X : SSet.{u}) :=
    innerHornFillers_ordinaryCoreCandidate X hX
  have hCY : innerHornFillers (ordinaryCoreCandidate Y : SSet.{u}) :=
    innerHornFillers_ordinaryCoreCandidate Y hY
  haveI := homotopyMap_faithful_of_mapping_weakEquivalences f hX hY hmap
  haveI := homotopyMap_full_of_mapping_weakEquivalences f hX hY hmap
  haveI : (leftMappingSpace (ordinaryCoreCandidate X : SSet.{u}) a b).KanComplex :=
    leftMappingSpace_kan hCX a b
  haveI : (leftMappingSpace (ordinaryCoreCandidate Y : SSet.{u})
      ((ordinaryCoreCandidateMap f).app (op ⦋0⦌) a)
      ((ordinaryCoreCandidateMap f).app (op ⦋0⦌) b)).KanComplex := leftMappingSpace_kan hCY _ _
  haveI : (leftMappingSpace X a.val b.val).KanComplex := leftMappingSpace_kan hX _ _
  haveI : (leftMappingSpace Y (f.app (op ⦋0⦌) a.val)
      (f.app (op ⦋0⦌) b.val)).KanComplex := leftMappingSpace_kan hY _ _
  have hf : SSet.KanComplex.W (leftMappingMap f a.val b.val) :=
    (SSet.weakEquivalence_iff_kanComplexW _).1 (hmap a.val b.val)
  apply (SSet.weakEquivalence_iff_kanComplexW _).2
  apply (SSet.KanComplex.W_iff _).2
  refine ⟨coreMappingMap_piZero_bijective f hX hY a b, ?_⟩
  rintro n v _ rfl
  exact coreMappingMap_mapπ_positive_bijective f hX hY a b hf n v

end

end DaggerOriginalCoreLeftMappingWeakEquivalences
