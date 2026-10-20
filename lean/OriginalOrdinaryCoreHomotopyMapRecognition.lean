import OriginalOrdinaryCoreHomotopyComparison
import OriginalUnitaryCoreOrdinaryEssentialSurjectivity

/-!
# The original ordinary core map on native homotopy categories

The exact native homotopy functor of the original core restriction is fully
faithful when the original ambient homotopy functor is fully faithful. Actual
core edge representatives of ambient isomorphisms supply its fullness. Native
component surjectivity supplies essential surjectivity on that same homotopy
category. This proves the one-categorical stage of ordinary recognition;
higher mapping-space full faithfulness and core weak equivalence are distinct
remaining requirements and are not replaced by homotopy-category equivalence.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial
open DaggerOriginalInnerHornFillers DaggerOriginalOrdinaryKanCoreSubcomplex
open DaggerOriginalOrdinaryKanCoreInnerHorns DaggerOriginalQuasicategoryPathEdgeRepresentatives
open DaggerOriginalOrdinaryCorePathGroupoid DaggerOriginalOrdinaryCoreHomotopyInclusion
open DaggerOriginalUnitaryCoreOrdinaryEssentialSurjectivity

universe u

namespace DaggerOriginalOrdinaryCoreHomotopyMapRecognition

noncomputable section

/-- The native homotopy functor of the same original core restriction, with all vertices retained.
-/
def coreHomotopyMap {X Y : SSet.{u}} (f : X ⟶ Y) :
    SSet.hoFunctor.obj (ordinaryCoreCandidate X : SSet.{u}) ⥤
      SSet.hoFunctor.obj (ordinaryCoreCandidate Y : SSet.{u}) :=
  (SSet.hoFunctor.map (ordinaryCoreCandidateMap f)).toFunctor

/-- The native functor has exactly the original restricted edge map. -/
theorem coreHomotopyMap_homMk {X Y : SSet.{u}} (f : X ⟶ Y)
    {x y : (ordinaryCoreCandidate X : SSet.{u}) _⦋0⦌} (e : SSet.Edge x y) :
    (coreHomotopyMap f).map (SSet.Truncated.HomotopyCategory.homMk e) =
      SSet.Truncated.HomotopyCategory.homMk (e.map (ordinaryCoreCandidateMap f)) := rfl

/-- The actual core path map commutes with the actual ambient path map and both inclusions. -/
theorem coreHomotopyMap_inclusion_map {X Y : SSet.{u}} (f : X ⟶ Y)
    (hX : innerHornFillers X)
    {x y : SSet.hoFunctor.obj (ordinaryCoreCandidate X : SSet.{u})} (p : x ⟶ y) :
    (coreHomotopyInclusion Y).map ((coreHomotopyMap f).map p) =
      (SSet.hoFunctor.map f).toFunctor.map ((coreHomotopyInclusion X).map p) := by
  obtain ⟨a, rfl⟩ := SSet.Truncated.HomotopyCategory.mk_surjective x
  obtain ⟨b, rfl⟩ := SSet.Truncated.HomotopyCategory.mk_surjective y
  obtain ⟨e, rfl⟩ := original_homMk_surjective (ordinaryCoreCandidate X : SSet.{u})
    (innerHornFillers_ordinaryCoreCandidate X hX) p
  let k : SSet.Edge (X := (ordinaryCoreCandidate X : SSet.{u})) a b := e
  change SSet.Truncated.HomotopyCategory.homMk
      (SSet.Edge.map (SSet.Edge.map k (ordinaryCoreCandidateMap f))
        (ordinaryCoreCandidate Y).ι) =
    SSet.Truncated.HomotopyCategory.homMk
      (SSet.Edge.map (SSet.Edge.map k (ordinaryCoreCandidate X).ι) f)
  apply congrArg SSet.Truncated.HomotopyCategory.homMk
  apply SSet.Edge.ext
  rfl

/-- Faithfulness of the original ambient homotopy functor is reflected to the original core. -/
theorem coreHomotopyMap_faithful {X Y : SSet.{u}} (f : X ⟶ Y) (hX : innerHornFillers X)
    [(SSet.hoFunctor.map f).toFunctor.Faithful] : (coreHomotopyMap f).Faithful where
  map_injective {x y} p q hpq := by
    have : (coreHomotopyInclusion X).Faithful := coreHomotopyInclusion_faithful X hX
    apply (coreHomotopyInclusion X).map_injective
    apply (SSet.hoFunctor.map f).toFunctor.map_injective
    rw [← coreHomotopyMap_inclusion_map f hX p, ← coreHomotopyMap_inclusion_map f hX q]
    exact congrArg (fun g ↦ (coreHomotopyInclusion Y).map g) hpq

/-- Fullness on original core paths follows by reflecting isomorphisms and lifting core edges. -/
theorem coreHomotopyMap_full {X Y : SSet.{u}} (f : X ⟶ Y)
    (hX : innerHornFillers X) (hY : innerHornFillers Y)
    [(SSet.hoFunctor.map f).toFunctor.Full] [(SSet.hoFunctor.map f).toFunctor.Faithful] :
    (coreHomotopyMap f).Full where
  map_surjective {x y} g := by
    obtain ⟨a, rfl⟩ := SSet.Truncated.HomotopyCategory.mk_surjective x
    obtain ⟨b, rfl⟩ := SSet.Truncated.HomotopyCategory.mk_surjective y
    have : IsIso g := core_path_isIso Y hY g
    obtain ⟨p, hp⟩ := (SSet.hoFunctor.map f).toFunctor.map_surjective
      (X := SSet.Truncated.HomotopyCategory.mk (V := (SSet.truncation 2).obj X) a.val)
      (Y := SSet.Truncated.HomotopyCategory.mk (V := (SSet.truncation 2).obj X) b.val)
      ((coreHomotopyInclusion Y).map g)
    have : IsIso ((SSet.hoFunctor.map f).toFunctor.map p) := by
      rw [hp]
      infer_instance
    have : IsIso p := isIso_of_fully_faithful (SSet.hoFunctor.map f).toFunctor p
    obtain ⟨e, he⟩ := core_edge_preimage_of_isIso X hX (x := a) (y := b) p
    refine ⟨SSet.Truncated.HomotopyCategory.homMk e, ?_⟩
    have : (coreHomotopyInclusion Y).Faithful := coreHomotopyInclusion_faithful Y hY
    apply (coreHomotopyInclusion Y).map_injective
    rw [coreHomotopyMap_inclusion_map f hX, he, hp]

/-- Surjectivity of the original core component map gives essential surjectivity on its own ho. -/
theorem coreHomotopyMap_essSurj {X Y : SSet.{u}} (f : X ⟶ Y) (hY : innerHornFillers Y)
    (hπ₀ : Function.Surjective (SSet.mapπ₀ (ordinaryCoreCandidateMap f))) :
    (coreHomotopyMap f).EssSurj where
  mem_essImage z := by
    obtain ⟨y, rfl⟩ := SSet.Truncated.HomotopyCategory.mk_surjective z
    obtain ⟨c, hc⟩ := hπ₀ (SSet.π₀.mk y)
    obtain ⟨x, rfl⟩ := SSet.π₀.mk_surjective c
    have hx : SSet.π₀.mk ((ordinaryCoreCandidateMap f).app (op ⦋0⦌) x) =
        SSet.π₀.mk y := by
      simpa only [SSet.mapπ₀_mk] using hc
    obtain ⟨e⟩ := core_homotopy_iso_of_pi0_eq Y hY hx
    exact ⟨SSet.Truncated.HomotopyCategory.mk x, ⟨e⟩⟩

/-- The original core ho map is an equivalence under ambient ho full faithfulness and core π₀. -/
theorem coreHomotopyMap_isEquivalence {X Y : SSet.{u}} (f : X ⟶ Y)
    (hX : innerHornFillers X) (hY : innerHornFillers Y)
    [(SSet.hoFunctor.map f).toFunctor.Full] [(SSet.hoFunctor.map f).toFunctor.Faithful]
    (hπ₀ : Function.Surjective (SSet.mapπ₀ (ordinaryCoreCandidateMap f))) :
    (coreHomotopyMap f).IsEquivalence :=
  ⟨coreHomotopyMap_faithful f hX, coreHomotopyMap_full f hX hY,
    coreHomotopyMap_essSurj f hY hπ₀⟩

/-- Ambient essential surjectivity lifts to the same original core homotopy category. -/
theorem coreHomotopyMap_essSurj_of_ambient {X Y : SSet.{u}} (f : X ⟶ Y)
    (hY : innerHornFillers Y) [(SSet.hoFunctor.map f).toFunctor.EssSurj] :
    (coreHomotopyMap f).EssSurj where
  mem_essImage z := by
    obtain ⟨y, rfl⟩ := SSet.Truncated.HomotopyCategory.mk_surjective z
    obtain ⟨x, ⟨e⟩⟩ := Functor.EssSurj.mem_essImage
      (F := (SSet.hoFunctor.map f).toFunctor)
      ((coreHomotopyInclusion Y).obj (SSet.Truncated.HomotopyCategory.mk y))
    obtain ⟨x, rfl⟩ := SSet.Truncated.HomotopyCategory.mk_surjective x
    let a : (ordinaryCoreCandidate X : SSet.{u}) _⦋0⦌ :=
      ⟨x, vertex_mem_ordinaryCoreCandidate X x⟩
    obtain ⟨k, _⟩ := core_edge_preimage_of_isIso Y hY
      (x := (ordinaryCoreCandidateMap f).app (op ⦋0⦌) a) (y := y) e.hom
    have : IsIso (SSet.Truncated.HomotopyCategory.homMk k) := core_homMk_isIso Y hY k
    exact ⟨SSet.Truncated.HomotopyCategory.mk a,
      ⟨asIso (SSet.Truncated.HomotopyCategory.homMk k)⟩⟩

/-- An ambient homotopy equivalence induces a homotopy equivalence of the original cores. -/
theorem coreHomotopyMap_isEquivalence_of_ambient {X Y : SSet.{u}} (f : X ⟶ Y)
    (hX : innerHornFillers X) (hY : innerHornFillers Y)
    [(SSet.hoFunctor.map f).toFunctor.IsEquivalence] :
    (coreHomotopyMap f).IsEquivalence :=
  ⟨coreHomotopyMap_faithful f hX, coreHomotopyMap_full f hX hY,
    coreHomotopyMap_essSurj_of_ambient f hY⟩

end

end DaggerOriginalOrdinaryCoreHomotopyMapRecognition
