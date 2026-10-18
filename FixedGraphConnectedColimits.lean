import FixedCategoryAdjunction
import FixedGraphStructural
import DaggerModels.DaggerGraphEvaluation
import DaggerModels.TypeFunctorSigma
import Mathlib.CategoryTheory.Limits.Connected

/-! Connected-colimit preservation and reflection by the ORIGINAL fixed graph adapter.
All homs, total-edge labels, dagger maps and cocone legs are retained. Only the
diagram shape is connected; the original object type may be empty or infinite.
-/

open CategoryTheory Limits Opposite DaggerModels
open DaggerFixedGraph DaggerFixedGraphPlacements DaggerFixedCategoryAdjunction

universe u

namespace DaggerFixedGraphConnectedColimits

noncomputable section

variable (O : Type u)

/-- Full original dagger maps provide the natural coordinate interchange. -/
def homDaggerIso (x y : O) : homEval O x y ≅ homEval O y x :=
  NatIso.ofComponents (fun G ↦ daggerIso G x y) (by
    intro G H f
    exact f.map_dagger x y)

/-- Every original ordered Hom evaluation preserves u-small colimits. -/
instance homEvalPreservesColimits (x y : O) :
    PreservesColimitsOfSize.{u, u} (homEval O x y) := by
  letI := chosenLinearOrder O
  rcases lt_trichotomy x y with h | h | h
  · exact upperHomEvalPreservesColimits O ⟨(x, y), h⟩
  · subst y
    exact diagonalHomEvalPreservesColimits O x
  · letI := upperHomEvalPreservesColimits O ⟨(y, x), h⟩
    exact preservesColimits_of_natIso (homDaggerIso O y x)

abbrev degreeEval (x y : O) (n : SimplexCategoryᵒᵖ) :
    FixedDaggerSimplicialGraph O ⥤ Type u :=
  homEval O x y ⋙ (evaluation SimplexCategoryᵒᵖ (Type u)).obj n

/-- The original labelled total edges, formed by two literal dependent sums. -/
abbrev edgeSigma (n : SimplexCategoryᵒᵖ) : FixedDaggerSimplicialGraph O ⥤ Type u :=
  TypeFunctorSigma.functor (fun x : O ↦
    TypeFunctorSigma.functor (fun y : O ↦ degreeEval O x y n))

def edgeSigmaIso (n : SimplexCategoryᵒᵖ) : edgeSigma O n ≅
    FixedDaggerSimplicialGraph.forget ⋙ DaggerGraphEvaluation.edges n := Iso.refl _

instance edgeSigmaPreservesColimits (n : SimplexCategoryᵒᵖ)
    (J : Type u) [SmallCategory J] : PreservesColimitsOfShape J (edgeSigma O n) := by
  letI (x y : O) : PreservesColimitsOfShape J (degreeEval O x y n) := inferInstance
  letI (x : O) : PreservesColimitsOfShape J
      (TypeFunctorSigma.functor (fun y : O ↦ degreeEval O x y n)) :=
    TypeFunctorSigma.preservesColimitsOfShape _ J
  exact TypeFunctorSigma.preservesColimitsOfShape _ J

instance totalEdgesPreservesColimits (n : SimplexCategoryᵒᵖ)
    (J : Type u) [SmallCategory J] : PreservesColimitsOfShape J
      (FixedDaggerSimplicialGraph.forget (O := O) ⋙ DaggerGraphEvaluation.edges n) :=
  preservesColimitsOfShape_of_natIso (edgeSigmaIso O n)

variable {O}

/-- Every original vertex cocone leg is id; connectedness concerns J, never O. -/
def vertexIsColimit {J : Type u} [SmallCategory J] [IsConnected J]
    {K : J ⥤ FixedDaggerSimplicialGraph O} (c : Cocone K) :
    IsColimit ((FixedDaggerSimplicialGraph.forget ⋙ DaggerGraphEvaluation.vertices).mapCocone c) :=
  isColimitConstCocone J O

variable (O)

instance verticesPreservesConnected (J : Type u) [SmallCategory J] [IsConnected J] :
    PreservesColimitsOfShape J
      (FixedDaggerSimplicialGraph.forget (O := O) ⋙ DaggerGraphEvaluation.vertices) where
  preservesColimit := ⟨fun {c} _ ↦ ⟨vertexIsColimit c⟩⟩

/-- The original presheaf equivalence detects the full graph cocone, including dagger. -/
instance forgetPreservesConnected (J : Type u) [SmallCategory J] [IsConnected J] :
    PreservesColimitsOfShape J (FixedDaggerSimplicialGraph.forget (O := O)) := by
  have preservation (k : DaggerGraphIndex.Objᵒᵖ) : PreservesColimitsOfShape J
      ((FixedDaggerSimplicialGraph.forget (O := O) ⋙ daggerGraphEquivalencePresheaf.functor) ⋙
        (evaluation DaggerGraphIndex.Objᵒᵖ (Type u)).obj k) := by
    cases k using Opposite.rec
    rename_i k
    cases k with
    | vertex =>
      exact preservesColimitsOfShape_of_natIso
        (Functor.isoWhiskerLeft FixedDaggerSimplicialGraph.forget
          DaggerGraphEvaluation.verticesIso)
    | edge n =>
      exact preservesColimitsOfShape_of_natIso
        (Functor.isoWhiskerLeft FixedDaggerSimplicialGraph.forget
          (DaggerGraphEvaluation.edgesIso (op n)))
  letI : PreservesColimitsOfShape J
      (FixedDaggerSimplicialGraph.forget (O := O) ⋙ daggerGraphEquivalencePresheaf.functor) :=
    preservesColimitsOfShape_of_evaluation _ J preservation
  exact preservesColimitsOfShape_of_reflects_of_preserves
    FixedDaggerSimplicialGraph.forget daggerGraphEquivalencePresheaf.functor

variable {O} {J : Type u} [SmallCategory J] [IsConnected J]
variable {K : J ⥤ FixedDaggerSimplicialGraph O} {c : Cocone K}

def ambientDesc (hc : IsColimit (FixedDaggerSimplicialGraph.forget.mapCocone c))
    (s : Cocone K) : c.pt.toGraph ⟶ s.pt.toGraph :=
  hc.desc (FixedDaggerSimplicialGraph.forget.mapCocone s)

/-- A shape object forces the SAME ambient desc to have object map id. -/
theorem ambientDesc_obj (hc : IsColimit (FixedDaggerSimplicialGraph.forget.mapCocone c))
    (s : Cocone K) : (ambientDesc hc s).obj = id := by
  exact congrArg (fun k : (K.obj (Classical.arbitrary J)).toGraph ⟶ s.pt.toGraph ↦ k.obj)
    (hc.fac (FixedDaggerSimplicialGraph.forget.mapCocone s) (Classical.arbitrary J))

def reflectedDesc (hc : IsColimit (FixedDaggerSimplicialGraph.forget.mapCocone c))
    (s : Cocone K) : c.pt ⟶ s.pt :=
  FixedDaggerSimplicialGraph.fromGraphMap (ambientDesc hc s) (ambientDesc_obj hc s)

theorem reflectedDesc_toGraph
    (hc : IsColimit (FixedDaggerSimplicialGraph.forget.mapCocone c)) (s : Cocone K) :
    FixedDaggerSimplicialGraph.toGraphMap (reflectedDesc hc s) = ambientDesc hc s :=
  congrArg Subtype.val
    (FixedDaggerSimplicialGraph.mapEquiv.apply_symm_apply ⟨_, ambientDesc_obj hc s⟩)

/-- Restrict the actual ambient universal morphism, retaining every full cocone leg. -/
def reflectIsColimit (hc : IsColimit (FixedDaggerSimplicialGraph.forget.mapCocone c)) :
    IsColimit c where
  desc := reflectedDesc hc
  fac s j := by
    apply FixedDaggerSimplicialCat.graph_map_injective
    change FixedDaggerSimplicialGraph.toGraphMap (c.ι.app j) ≫
      FixedDaggerSimplicialGraph.toGraphMap (reflectedDesc hc s) =
        FixedDaggerSimplicialGraph.toGraphMap (s.ι.app j)
    rw [reflectedDesc_toGraph]
    exact hc.fac (FixedDaggerSimplicialGraph.forget.mapCocone s) j
  uniq s m hm := by
    apply FixedDaggerSimplicialCat.graph_map_injective
    rw [reflectedDesc_toGraph]
    exact hc.uniq (FixedDaggerSimplicialGraph.forget.mapCocone s)
      (FixedDaggerSimplicialGraph.toGraphMap m) (fun j ↦
        congrArg FixedDaggerSimplicialGraph.toGraphMap (hm j))

instance forgetReflectsConnected : ReflectsColimitsOfShape J
    (FixedDaggerSimplicialGraph.forget (O := O)) where
  reflectsColimit := ⟨fun hc ↦ ⟨reflectIsColimit hc⟩⟩

variable (O)

abbrev fixedWords := free O ⋙ FixedDaggerSimplicialCat.forgetGraph O

abbrev ambientWords := FreeDaggerSimplicialCategory.functor ⋙ DaggerSimplicialCat.forgetGraph

/-- The full original finite-path square; components are identity graph isomorphisms. -/
def wordSquareIso : fixedWords O ⋙ FixedDaggerSimplicialGraph.forget ≅
    FixedDaggerSimplicialGraph.forget ⋙ ambientWords :=
  NatIso.ofComponents (fun G ↦ Iso.refl _) (by
    intro G H f
    exact FixedDaggerSimplicialCat.forgetGraph_toGraph_map ((free O).map f))

end

end DaggerFixedGraphConnectedColimits
