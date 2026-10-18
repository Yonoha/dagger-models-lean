import FixedCategoryAdjunction
import FixedGraphStructural
import DaggerModels.DaggerHomKernel

/-! The semantic kernel over actual fixed-O cocones, starting with the original fixed graph
colimit and the same free category. No ambient category colimit or new word laws are used. -/

open CategoryTheory Limits DaggerModels

universe u

namespace DaggerFixedCategoryColimits.Kernel

noncomputable section

variable {O : Type u} {J : Type u} [SmallCategory J] (K : J ⥤ FixedDaggerSimplicialCat O)

def graph : FixedDaggerSimplicialGraph O := colimit (K ⋙ FixedDaggerSimplicialCat.forgetGraph O)

def free : FixedDaggerSimplicialCat O := (DaggerFixedCategoryAdjunction.free O).obj (graph K)

def freeLift (s : Cocone K) : free K ⟶ s.pt :=
  ((DaggerFixedCategoryAdjunction.adjunction O).homEquiv (graph K) s.pt).symm
    (colimit.desc (K ⋙ FixedDaggerSimplicialCat.forgetGraph O)
      ((FixedDaggerSimplicialCat.forgetGraph O).mapCocone s))

def leg (j : J) : (FixedDaggerSimplicialCat.forgetGraph O).obj (K.obj j) ⟶
    (FixedDaggerSimplicialCat.forgetGraph O).obj (free K) :=
  colimit.ι (K ⋙ FixedDaggerSimplicialCat.forgetGraph O) j ≫
    (DaggerFixedCategoryAdjunction.adjunction O).unit.app (graph K)

theorem leg_freeLift (s : Cocone K) (j : J) :
    leg K j ≫ (FixedDaggerSimplicialCat.forgetGraph O).map (freeLift K s) =
      (FixedDaggerSimplicialCat.forgetGraph O).map (s.ι.app j) := by
  have h : (DaggerFixedCategoryAdjunction.adjunction O).unit.app (graph K) ≫
      (FixedDaggerSimplicialCat.forgetGraph O).map (freeLift K s) =
      colimit.desc (K ⋙ FixedDaggerSimplicialCat.forgetGraph O)
        ((FixedDaggerSimplicialCat.forgetGraph O).mapCocone s) :=
    ((DaggerFixedCategoryAdjunction.adjunction O).homEquiv (graph K) s.pt).apply_symm_apply _
  unfold leg
  rw [Category.assoc, h]
  exact colimit.ι_desc ((FixedDaggerSimplicialCat.forgetGraph O).mapCocone s) j

theorem ambient_leg_freeLift (s : Cocone K) (j : J) :
    FixedDaggerSimplicialGraph.toGraphMap (leg K j) ≫
      DaggerSimplicialCat.forgetGraph.map (freeLift K s).val =
        DaggerSimplicialCat.forgetGraph.map (s.ι.app j).val := by
  simpa only [Functor.map_comp, FixedDaggerSimplicialGraph.forget,
    FixedDaggerSimplicialCat.forgetGraph_toGraph_map] using
      congrArg (FixedDaggerSimplicialGraph.forget (O := O)).map (leg_freeLift K s j)

def rel (n : SimplexCategoryᵒᵖ) (x y : O)
    (f g : ((free K).enriched.Hom x y).obj n) : Prop :=
  DaggerSimplicialCat.HomKernel.rel (fun s : Cocone K ↦ (freeLift K s).val) n x y f g

theorem rel_id (j : J) (n : SimplexCategoryᵒᵖ) (x : O) :
    rel K n x x (((leg K j).map x x).app n ((K.obj j).enriched.id x |>.app n PUnit.unit))
      ((free K).enriched.id x |>.app n PUnit.unit) := by
  intro s
  have h : ∀ x : O,
      (((FixedDaggerSimplicialGraph.toGraphMap (leg K j) ≫
        DaggerSimplicialCat.forgetGraph.map (freeLift K s).val).map x x).app n
          ((K.obj j).enriched.id x |>.app n PUnit.unit)) =
      ((s.pt.enriched.id ((FixedDaggerSimplicialGraph.toGraphMap (leg K j) ≫
        DaggerSimplicialCat.forgetGraph.map (freeLift K s).val).obj x)).app n PUnit.unit) := by
    rw [ambient_leg_freeLift]
    intro x
    exact congrArg (fun a ↦ a.app n PUnit.unit) ((s.ι.app j).val.map_id x)
  exact (h x).trans
    (congrArg (fun a ↦ a.app n PUnit.unit) ((freeLift K s).val.map_id x)).symm

theorem rel_comp (j : J) (n : SimplexCategoryᵒᵖ) (x y z : O)
    (f : ((K.obj j).enriched.Hom x y).obj n) (g : ((K.obj j).enriched.Hom y z).obj n) :
    rel K n x z (((leg K j).map x z).app n ((K.obj j).enriched.comp x y z |>.app n (f, g)))
      ((free K).enriched.comp x y z |>.app n
        (((leg K j).map x y).app n f, ((leg K j).map y z).app n g)) := by
  intro s
  have h : ∀ (x y z : O) (f : ((K.obj j).enriched.Hom x y).obj n)
      (g : ((K.obj j).enriched.Hom y z).obj n),
      ((FixedDaggerSimplicialGraph.toGraphMap (leg K j) ≫
        DaggerSimplicialCat.forgetGraph.map (freeLift K s).val).map x z).app n
          ((K.obj j).enriched.comp x y z |>.app n (f, g)) =
      (s.pt.enriched.comp
        ((FixedDaggerSimplicialGraph.toGraphMap (leg K j) ≫
          DaggerSimplicialCat.forgetGraph.map (freeLift K s).val).obj x)
        ((FixedDaggerSimplicialGraph.toGraphMap (leg K j) ≫
          DaggerSimplicialCat.forgetGraph.map (freeLift K s).val).obj y)
        ((FixedDaggerSimplicialGraph.toGraphMap (leg K j) ≫
          DaggerSimplicialCat.forgetGraph.map (freeLift K s).val).obj z)).app n
        (((FixedDaggerSimplicialGraph.toGraphMap (leg K j) ≫
          DaggerSimplicialCat.forgetGraph.map (freeLift K s).val).map x y).app n f,
         ((FixedDaggerSimplicialGraph.toGraphMap (leg K j) ≫
          DaggerSimplicialCat.forgetGraph.map (freeLift K s).val).map y z).app n g) := by
    rw [ambient_leg_freeLift]
    intro x y z f g
    exact congrArg (fun a ↦ a.app n (f, g)) ((s.ι.app j).val.map_comp x y z)
  exact (h x y z f g).trans
    (congrArg (fun a ↦ a.app n
      (((leg K j).map x y).app n f, ((leg K j).map y z).app n g))
        ((freeLift K s).val.map_comp x y z)).symm

def relation : DaggerSimplicialCat.HomQuotient.StableHomRel (free K).toCat where
  rel := rel K
  map_rel {_n _m} α {x y} {_f _g} h :=
    DaggerSimplicialCat.HomKernel.rel_map (fun s ↦ (freeLift K s).val) α x y h
  dagger_rel {n x y _f _g} h :=
    DaggerSimplicialCat.HomKernel.rel_dagger (fun s ↦ (freeLift K s).val) n x y h

end

end DaggerFixedCategoryColimits.Kernel
