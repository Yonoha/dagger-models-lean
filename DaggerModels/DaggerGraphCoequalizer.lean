import DaggerModels.DaggerGraphDescent
import Mathlib.CategoryTheory.Limits.Shapes.SplitCoequalizer
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers

/-!
# Coequalizers with a split underlying dagger graph

Once the quotient has been constructed as an actual dagger simplicial category,
an enriched cofork whose underlying graph is split is a genuine coequalizer.
Its graph factorization descends using the graph section, which need not preserve
units or composition. This supplies the universal-property step of Part I
`bg.lem.presentable`; the quotient enrichment is constructed separately.
-/

open CategoryTheory CategoryTheory.Limits

universe u

namespace DaggerModels.DaggerSimplicialCat.GraphCoequalizer

variable {A B Q : DaggerSimplicialCat.{u, u}} {f g : A ⟶ B}
  (π : B ⟶ Q) (condition : f ≫ π = g ≫ π)
  (t : IsSplitCoequalizer (forgetGraph.map f) (forgetGraph.map g) (forgetGraph.map π))

/-- The actual enriched cofork is a colimit when its graph image is split. -/
def isColimit : IsColimit (Cofork.ofπ π condition) :=
  Cofork.IsColimit.mk' _ fun c ↦ by
    have hc : forgetGraph.map f ≫ forgetGraph.map c.π =
        forgetGraph.map g ≫ forgetGraph.map c.π := by
      rw [← forgetGraph.map_comp, c.condition, forgetGraph.map_comp]
    have hfac : forgetGraph.map π ≫ (t.rightSection ≫ forgetGraph.map c.π) =
        forgetGraph.map c.π :=
      Cofork.IsColimit.π_desc (t := Cofork.ofπ (forgetGraph.map c.π) hc) t.isCoequalizer
    let d := GraphDescent.lift π t.rightSection t.rightSection_π
      (t.rightSection ≫ forgetGraph.map c.π) c.π hfac
    refine ⟨d, GraphDescent.comp_lift π t.rightSection t.rightSection_π
      (t.rightSection ≫ forgetGraph.map c.π) c.π hfac, ?_⟩
    intro m hm
    change π ≫ m = c.π at hm
    apply forgetGraph.map_injective
    change forgetGraph.map m = t.rightSection ≫ forgetGraph.map c.π
    calc
      _ = (t.rightSection ≫ forgetGraph.map π) ≫ forgetGraph.map m := by
        rw [t.rightSection_π, Category.id_comp]
      _ = _ := by rw [Category.assoc, ← forgetGraph.map_comp, hm]

/-- This constructed cofork supplies the required source coequalizer. -/
def hasCoequalizer : HasCoequalizer f g :=
  HasColimit.mk ⟨Cofork.ofπ π condition, isColimit π condition t⟩

/-- The graph forgetful functor preserves this pair's actual coequalizers. -/
def preservesColimit : PreservesColimit (parallelPair f g) forgetGraph :=
  preservesColimit_of_preserves_colimit_cocone (isColimit π condition t)
    ((isColimitMapCoconeCoforkEquiv forgetGraph condition).symm t.isCoequalizer)

end DaggerModels.DaggerSimplicialCat.GraphCoequalizer
