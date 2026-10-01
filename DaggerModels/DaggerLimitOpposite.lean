import DaggerModels.SimplicialObjectAdjunctions
import DaggerModels.DaggerStructureFromOpposite

/-!
Part I `bg.lem.creation`: construct the actual dagger
on the apex of a given ordinary simplicial-category limit cone. No existence
of ordinary limits or created-limit instance is assumed or asserted here.
-/

open CategoryTheory Limits Opposite Functor

universe o v w w'

noncomputable section

namespace DaggerModels.DaggerSimplicialCat.LimitOpposite

variable {J : Type w} [Category.{w'} J] (K : J ⥤ DaggerSimplicialCat.{o, v})
  (c : Cone (K ⋙ forget)) (hc : IsLimit c)

/-- Composing each ordinary projection with the original diagram dagger gives a cone. -/
def daggerCone : Cone ((K ⋙ forget) ⋙ SimplicialCat.oppositeFunctor) :=
  (Cones.postcompose (whiskerLeft K daggerNatural)).obj c

/-- The ordinary opposite preserves this particular given limit. -/
def oppositeIsLimit : IsLimit (SimplicialCat.oppositeFunctor.mapCone c) :=
  isLimitOfPreserves SimplicialCat.oppositeFunctor hc

/-- The induced enriched functor to the actual ordinary opposite. -/
def induced : c.pt ⟶ SimplicialCat.opposite c.pt :=
  (oppositeIsLimit K c hc).lift (daggerCone K c)

theorem induced_fac (j : J) :
    induced K c hc ≫ SimplicialCat.oppositeMap (c.π.app j) =
      c.π.app j ≫ daggerNatural.app (K.obj j) :=
  (oppositeIsLimit K c hc).fac (daggerCone K c) j

/-- The induced map is involutive with the actual double-opposite identification. -/
theorem induced_square :
    induced K c hc ≫ SimplicialCat.oppositeMap (induced K c hc) ≫
      SimplicialCat.doubleOppositeHom c.pt = 𝟙 c.pt := by
  apply hc.hom_ext
  intro j
  let d := induced K c hc
  let π := c.π.app j
  let δ := daggerNatural.app (K.obj j)
  have hfac : d ≫ SimplicialCat.oppositeMap π = π ≫ δ := induced_fac K c hc j
  have hnat : SimplicialCat.doubleOppositeHom c.pt ≫ π =
      SimplicialCat.oppositeMap (SimplicialCat.oppositeMap π) ≫
        SimplicialCat.doubleOppositeHom (forget.obj (K.obj j)) :=
    (SimplicialCat.doubleOppositeNatIso.hom.naturality π).symm
  have hopfac := congrArg (SimplicialCat.oppositeFunctor.map) hfac
  simp only [Functor.map_comp] at hopfac
  change (d ≫ SimplicialCat.oppositeMap d ≫ SimplicialCat.doubleOppositeHom c.pt) ≫ π =
    𝟙 c.pt ≫ π
  calc
    _ = d ≫ SimplicialCat.oppositeMap d ≫
        SimplicialCat.oppositeMap (SimplicialCat.oppositeMap π) ≫
          SimplicialCat.doubleOppositeHom (forget.obj (K.obj j)) := by
      simp only [Category.assoc]
      rw [hnat]
    _ = d ≫ SimplicialCat.oppositeMap π ≫ SimplicialCat.oppositeMap δ ≫
        SimplicialCat.doubleOppositeHom (forget.obj (K.obj j)) := by
      simpa only [Category.assoc] using congrArg
        (fun a ↦ d ≫ a ≫ SimplicialCat.doubleOppositeHom (forget.obj (K.obj j))) hopfac
    _ = π ≫ δ ≫ SimplicialCat.oppositeMap δ ≫
        SimplicialCat.doubleOppositeHom (forget.obj (K.obj j)) := by
      rw [← Category.assoc d, hfac]
      simp only [Category.assoc]
    _ = 𝟙 c.pt ≫ π := by
      rw [show δ ≫ SimplicialCat.oppositeMap δ ≫
        SimplicialCat.doubleOppositeHom (forget.obj (K.obj j)) = 𝟙 _ from
          daggerNatural_square (K.obj j)]
      simp

/-- Since objects preserves this limit, its projections jointly determine every object. -/
theorem induced_obj (X : c.pt.Obj) : (induced K c hc).obj X = op X := by
  letI : PreservesLimitsOfSize.{w', w} SimplicialCat.objects.{o, v} :=
    SimplicialCat.objectsPreservesLimitsOfSize
  have ht := isLimitOfPreserves SimplicialCat.objects hc
  have h : (fun _ : PUnit.{o + 1} ↦ ((induced K c hc).obj X).unop) =
      (fun _ : PUnit.{o + 1} ↦ X) := by
    apply ht.hom_ext
    intro j
    funext t
    have hj := congrArg (fun f ↦ f.obj X) (induced_fac K c hc j)
    exact congrArg Opposite.unop hj
  exact congrArg Opposite.op (congrFun h PUnit.unit)

end DaggerModels.DaggerSimplicialCat.LimitOpposite
