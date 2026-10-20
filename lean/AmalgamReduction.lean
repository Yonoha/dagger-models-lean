import AmalgamObjectData
import Mathlib.Logic.Relation
import Mathlib.Order.WellFounded

/-! The literal reduction already defining the two-color enriched hom quotient. -/

open CategoryTheory DaggerModels
open DaggerAmalgamPresentation

universe u

namespace DaggerAmalgamReduction

variable (B B' : SimplicialCat.{u, u}) (b : B.Obj) (b' : B'.Obj)

/-- Exactly the existing contextual one-step relation, with its original orientation. -/
abbrev Red (q : SimplexCategoryᵒᵖ) (a z : Objects B B' b b') :
    Path B B' b b' q a z → Path B B' b b' q a z → Prop :=
  @HomRel.CompClosure (SimplicialEnrichment.At (free B B' b b').Obj q) _
    (SimplicialCat.HomQuotient.degreeRel (relations B B' b b') q) a z

theorem length_drop {q : SimplexCategoryᵒᵖ} {a z : Objects B B' b b'}
    {p p' : Path B B' b b' q a z} (h : Red B B' b b' q a z p p') :
    p'.length + 1 = p.length := by
  rcases h with ⟨s, t, l, r, r', v, h⟩
  cases h <;>
    change (l.comp (Quiver.Path.comp _ v)).length + 1 =
      (l.comp (Quiver.Path.comp _ v)).length <;>
    simp [factorPath, SimplicialColimitsFree.Paths.inclusion, Quiver.Hom.toPath] <;> omega

theorem length_lt {q : SimplexCategoryᵒᵖ} {a z : Objects B B' b b'}
    {p p' : Path B B' b b' q a z} (h : Red B B' b b' q a z p p') :
    p'.length < p.length := by
  have := length_drop B B' b b' h
  omega

/-- The reverse relation is well-founded, on every actual dependent Hom path. -/
theorem reverse_wellFounded (q : SimplexCategoryᵒᵖ) (a z : Objects B B' b b') :
    WellFounded (fun p' p : Path B B' b b' q a z ↦ Red B B' b b' q a z p p') :=
  Subrelation.wf (fun h ↦ length_lt B B' b b' h) (measure Quiver.Path.length).wf

end DaggerAmalgamReduction
