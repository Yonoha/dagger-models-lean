import OriginalOrdinaryCoreHomotopyInclusion

/-!
# Native homotopy comparison with the ordinary categorical core

Factor the native homotopy-category functor of the same original inclusion
through Mathlib's ordinary categorical Core. Actual triangle lifting proves
faithfulness. Original edge representatives of ambient isomorphisms prove
fullness. All vertices are retained literally, so the object map is bijective.
This is the ordinary comparison used in Joyal's Theory of Quasi-Categories,
Proposition 4.20; higher outer horns and derived dagger recognition remain open.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial
open DaggerOriginalOrdinaryKanCoreSubcomplex
open DaggerOriginalInnerHornFillers
open DaggerOriginalOrdinaryCorePathGroupoid
open DaggerOriginalOrdinaryCoreHomotopyInclusion

universe u

namespace DaggerOriginalOrdinaryCoreHomotopyComparison

noncomputable section

/-- The actual original core inclusion on ho, factored through the native categorical core. -/
def coreHomotopyComparison (X : SSet.{u}) (hX : innerHornFillers X) :
    SSet.hoFunctor.obj (ordinaryCoreCandidate X : SSet.{u}) ⥤ Core (SSet.hoFunctor.obj X) := by
  letI := corePathGroupoid X hX
  exact Core.functorToCore (coreHomotopyInclusion X)

/-- Forgetting the categorical-core factor gives exactly the original native inclusion on ho. -/
theorem coreHomotopyComparison_forget (X : SSet.{u}) (hX : innerHornFillers X) :
    coreHomotopyComparison X hX ⋙ Core.inclusion (SSet.hoFunctor.obj X) =
      coreHomotopyInclusion X := rfl

/-- The comparison has precisely the original core edge map on the underlying morphisms. -/
theorem coreHomotopyComparison_homMk (X : SSet.{u}) (hX : innerHornFillers X)
    {x y : (ordinaryCoreCandidate X : SSet.{u}).obj (op ⦋0⦌)} (e : SSet.Edge x y) :
    ((coreHomotopyComparison X hX).map (SSet.Truncated.HomotopyCategory.homMk e)).iso.hom =
      SSet.Truncated.HomotopyCategory.homMk (e.map (ordinaryCoreCandidate X).ι) := rfl

/-- The literal comparison reflects arbitrary native path classes. -/
theorem coreHomotopyComparison_faithful (X : SSet.{u}) (hX : innerHornFillers X) :
    (coreHomotopyComparison X hX).Faithful where
  map_injective {x y} f g h := by
    apply (coreHomotopyInclusion_faithful X hX).map_injective
    exact congrArg
      (fun k : (coreHomotopyComparison X hX).obj x ⟶
        (coreHomotopyComparison X hX).obj y ↦ k.iso.hom) h

/-- Every actual isomorphism in the target categorical core has an original core path preimage. -/
theorem coreHomotopyComparison_full (X : SSet.{u}) (hX : innerHornFillers X) :
    (coreHomotopyComparison X hX).Full where
  map_surjective {x y} f := by
    obtain ⟨a, rfl⟩ := SSet.Truncated.HomotopyCategory.mk_surjective x
    obtain ⟨b, rfl⟩ := SSet.Truncated.HomotopyCategory.mk_surjective y
    obtain ⟨e, he⟩ := core_edge_preimage_of_isIso X hX (x := a) (y := b) f.iso.hom
    refine ⟨SSet.Truncated.HomotopyCategory.homMk e, ?_⟩
    apply Core.hom_ext
    exact he

/-- The actual comparison retains every original vertex once, with no object replacement. -/
theorem coreHomotopyComparison_obj_bijective (X : SSet.{u}) (hX : innerHornFillers X) :
    Function.Bijective (coreHomotopyComparison X hX).obj := by
  constructor
  · intro a b h
    obtain ⟨x, rfl⟩ := SSet.Truncated.HomotopyCategory.mk_surjective a
    obtain ⟨y, rfl⟩ := SSet.Truncated.HomotopyCategory.mk_surjective b
    have hv : x.val = y.val := congrArg
      (fun z : Core (SSet.hoFunctor.obj X) ↦ (SSet.hoFunctor.obj.equiv X) z.of) h
    have hxy : x = y := Subtype.ext hv
    rw [hxy]
  · rintro ⟨a⟩
    obtain ⟨x, rfl⟩ := SSet.Truncated.HomotopyCategory.mk_surjective a
    exact ⟨SSet.Truncated.HomotopyCategory.mk ⟨x, vertex_mem_ordinaryCoreCandidate X x⟩, rfl⟩

/-- In particular the native comparison is essentially surjective. -/
theorem coreHomotopyComparison_essSurj (X : SSet.{u}) (hX : innerHornFillers X) :
    (coreHomotopyComparison X hX).EssSurj where
  mem_essImage z := by
    obtain ⟨a, ha⟩ := (coreHomotopyComparison_obj_bijective X hX).surjective z
    exact ⟨a, ⟨eqToIso ha⟩⟩

/-- The exact native comparison is an equivalence, without assuming higher outer-horn fillers. -/
theorem coreHomotopyComparison_isEquivalence (X : SSet.{u}) (hX : innerHornFillers X) :
    (coreHomotopyComparison X hX).IsEquivalence :=
  ⟨coreHomotopyComparison_faithful X hX, coreHomotopyComparison_full X hX,
    coreHomotopyComparison_essSurj X hX⟩

/-- An equivalence whose forward functor is precisely the proved native comparison. -/
def coreHomotopyEquivalence (X : SSet.{u}) (hX : innerHornFillers X) :
    SSet.hoFunctor.obj (ordinaryCoreCandidate X : SSet.{u}) ≌ Core (SSet.hoFunctor.obj X) := by
  letI := coreHomotopyComparison_isEquivalence X hX
  exact (coreHomotopyComparison X hX).asEquivalence

/-- The forward functor of the equivalence is the same original comparison. -/
theorem coreHomotopyEquivalence_functor (X : SSet.{u}) (hX : innerHornFillers X) :
    (coreHomotopyEquivalence X hX).functor = coreHomotopyComparison X hX := rfl

end

end DaggerOriginalOrdinaryCoreHomotopyComparison
