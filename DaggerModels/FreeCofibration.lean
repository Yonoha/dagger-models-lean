import DaggerModels.FreeDagger
import Mathlib.CategoryTheory.Functor.EpiMono
import Mathlib.CategoryTheory.MorphismProperty.Retract

/-!
# Elementary closure properties of free cofibrations

The predicate remains the one in Part I, `dj.def.free-cof`: a monomorphism in the
dagger category with free dagger action on new nondegenerate positive-dimensional
simplices. The free--forgetful adjunction identifies its monicity condition with
underlying simplicial monicity. We prove identities, composition, and retracts
preserve the predicate. The cellular characterization in `dj.lem.free-cof` is not
asserted here.
-/

open CategoryTheory Simplicial Opposite

universe u

namespace DaggerModels.DaggerSSet

/-- Monicity in the dagger category agrees with underlying simplicial monicity. -/
theorem mono_iff_mono_hom {X Y : DaggerSSet.{u}} (f : X ⟶ Y) :
    Mono f ↔ Mono f.hom := by
  let : forget.{u}.PreservesMonomorphisms :=
    Functor.preservesMonomorphisms_of_adjunction freeDaggerAdjunction
  exact (forget.mono_map_iff_mono f).symm

/-- An identity introduces no new simplices. -/
theorem freeCofibration_id (X : DaggerSSet.{u}) : FreeCofibration (𝟙 X) := by
  refine ⟨inferInstance, ?_⟩
  intro n hn x hx hnew
  exact False.elim (hnew ⟨x, rfl⟩)

/-- Composing free cofibrations preserves the free action on new simplices. -/
theorem FreeCofibration.comp {X Y Z : DaggerSSet.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    (hf : FreeCofibration f) (hg : FreeCofibration g) : FreeCofibration (f ≫ g) := by
  let : Mono f := hf.1
  let : Mono g := hg.1
  let : Mono g.hom := (mono_iff_mono_hom g).1 hg.1
  refine ⟨inferInstance, ?_⟩
  intro n hn z hz hnew
  by_cases hgz : z ∈ Set.range (g.hom.app (op ⦋n⦌))
  · obtain ⟨y, rfl⟩ := hgz
    have hy : y ∈ Y.toSSet.nonDegenerate n :=
      (SSet.nonDegenerate_iff_of_mono g.hom y).1 hz
    have hynew : y ∉ Set.range (f.hom.app (op ⦋n⦌)) := by
      rintro ⟨x, rfl⟩
      exact hnew ⟨x, rfl⟩
    intro hfix
    apply hf.2 n hn y hy hynew
    apply (CategoryTheory.mono_iff_injective (g.hom.app (op ⦋n⦌))).1 inferInstance
    exact (g.dagger_comm y).trans hfix
  · exact hg.2 n hn z hz hgz

/-- A retract of a free cofibration is free, as in the end of `dj.lem.free-cof`. -/
theorem FreeCofibration.of_retract {X Y Z W : DaggerSSet.{u}}
    {f : X ⟶ Y} {g : Z ⟶ W} (h : RetractArrow f g)
    (hg : FreeCofibration g) : FreeCofibration f := by
  have hf : Mono f := MorphismProperty.of_retract
    (P := MorphismProperty.monomorphisms DaggerSSet.{u}) h hg.1
  let : Mono h.i.right.hom := (mono_iff_mono_hom h.i.right).1 inferInstance
  refine ⟨hf, ?_⟩
  intro n hn y hy hnew hfix
  have hiy : h.i.right.hom.app (op ⦋n⦌) y ∈ W.toSSet.nonDegenerate n :=
    (SSet.nonDegenerate_iff_of_mono h.i.right.hom y).2 hy
  have hiynew : h.i.right.hom.app (op ⦋n⦌) y ∉ Set.range (g.hom.app (op ⦋n⦌)) := by
    rintro ⟨z, hz⟩
    apply hnew
    refine ⟨h.r.left.hom.app (op ⦋n⦌) z, ?_⟩
    calc
      f.hom.app _ (h.r.left.hom.app _ z) = h.r.right.hom.app _ (g.hom.app _ z) :=
        congrArg (fun k : Z ⟶ Y ↦ k.hom.app (op ⦋n⦌) z) h.r_w
      _ = h.r.right.hom.app _ (h.i.right.hom.app _ y) := congrArg _ hz
      _ = y := congrArg (fun k : Y ⟶ Y ↦ k.hom.app (op ⦋n⦌) y) h.retract_right
  apply hg.2 n hn _ hiy hiynew
  exact (h.i.right.dagger_comm y).symm.trans (congrArg _ hfix)

end DaggerModels.DaggerSSet
