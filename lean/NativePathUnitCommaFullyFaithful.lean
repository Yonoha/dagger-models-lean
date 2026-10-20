import NativePathUnitQuiverCovering

/-! Every actual comma morphism lifts uniquely as a path in the actual generator covering. -/
set_option autoImplicit false
open CategoryTheory
open DaggerNativeFreePathCompletionQuiverBridge
open DaggerNativePathUnitLiftedQuiver DaggerNativePathUnitQuiverCovering
universe u
namespace DaggerNativePathUnitCommaFullyFaithful
noncomputable section

variable (V : Type u) [Quiver.{u + 1} V] (d : Quiver.FreeGroupoid V)

theorem commaFunctor_map_injective {x y : Vertex V d} :
    Function.Injective (fun p : Quiver.Path x y ↦ (commaFunctor V d).map p) := by
  intro p q hpq
  have hh := congrArg (fun f ↦ f.right) hpq
  have he : (projection V d).mapPath p = (projection V d).mapPath q :=
    (commaFunctor_map_right V d p).symm.trans (hh.trans (commaFunctor_map_right V d q))
  have hs : (projection V d).pathStar x ⟨y, p⟩ =
      (projection V d).pathStar x ⟨y, q⟩ := congrArg (Sigma.mk y.right) he
  have hi := (projection_pathStar_bijective V d x).1 hs
  exact eq_of_heq (Sigma.mk.inj_iff.mp hi).2

theorem commaFunctor_map_surjective {x y : Vertex V d}
    (f : (commaFunctor V d).obj x ⟶ (commaFunctor V d).obj y) :
    ∃ p : Quiver.Path x y, (commaFunctor V d).map p = f := by
  rcases y with ⟨v, hy⟩
  obtain ⟨⟨⟨w, hz⟩, p⟩, hp⟩ := (projection_pathStar_bijective V d x).2 ⟨v, f.right⟩
  change (⟨w, (projection V d).mapPath p⟩ : Quiver.PathStar x.right) = ⟨v, f.right⟩ at hp
  obtain ⟨hv, hp⟩ := Sigma.mk.inj_iff.mp hp
  subst v
  have hp' : (projection V d).mapPath p = f.right := eq_of_heq hp
  have ht := StructuredArrow.w ((commaFunctor V d).map p)
  have hf := StructuredArrow.w f
  change x.hom ≫ (pathUnit V).map (((commaFunctor V d).map p).right) = hz at ht
  change x.hom ≫ (pathUnit V).map f.right = hy at hf
  have hright := commaFunctor_map_right V d p
  rw [hright, hp'] at ht
  have hhy : hy = hz := hf.symm.trans ht
  subst hy
  refine ⟨p, StructuredArrow.hom_ext _ _ ?_⟩
  exact (commaFunctor_map_right V d p).trans hp'

def commaFullyFaithful : (commaFunctor V d).FullyFaithful where
  preimage f := Classical.choose (commaFunctor_map_surjective V d f)
  map_preimage f := Classical.choose_spec (commaFunctor_map_surjective V d f)
  preimage_map p := commaFunctor_map_injective V d
    (Classical.choose_spec (commaFunctor_map_surjective V d ((commaFunctor V d).map p)))

instance commaFunctor_isEquivalence : (commaFunctor V d).IsEquivalence := by
  letI := (commaFullyFaithful V d).full
  letI := (commaFullyFaithful V d).faithful
  letI : (commaFunctor V d).EssSurj :=
    { mem_essImage := fun x ↦ ⟨vertexOfComma V d x, ⟨Iso.refl x⟩⟩ }
  exact {}

end
end DaggerNativePathUnitCommaFullyFaithful
