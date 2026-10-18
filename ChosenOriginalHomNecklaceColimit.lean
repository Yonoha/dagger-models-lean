import ChosenFlagOriginalHomNaturality
import ChosenNecklaceFlagHomIso

open CategoryTheory Functor Limits EnrichedCategory MonoidalCategory Opposite Simplicial

universe u

namespace DaggerChosenRigidificationNecklace

noncomputable section

open NecklaceCode NecklaceThickening

def necklaceInverseFirst (T : NecklaceCode) :
    (chosenNecklaceIso T).inv.obj (outerLeft T) = RV T.toSSet T.first :=
  chosenNecklaceIso_inv_objects T (outerLeft T)

def necklaceInverseLast (T : NecklaceCode) :
    (chosenNecklaceIso T).inv.obj (outerRight T) = RV T.toSSet T.last :=
  chosenNecklaceIso_inv_objects T (outerRight T)

/-- Original chosen-C outer Hom coordinates, using the specified inverse and both endpoint casts. -/
def necklaceOriginalOuterHomIso (T : NecklaceCode) :
    flagSSet.{u} T ≅ (RV T.toSSet T.first ⟶[SSet.{u}] RV T.toSSet T.last) :=
  outerFlagIso T ≪≫
    DaggerSimplicialIsoHoms.homIso (chosenNecklaceIso T).symm (outerLeft T) (outerRight T) ≪≫
      eqToIso (by
        change ((chosenNecklaceIso T).inv.obj (outerLeft T) ⟶[SSet.{u}]
          (chosenNecklaceIso T).inv.obj (outerRight T)) = _
        rw [necklaceInverseFirst T, necklaceInverseLast T])

theorem necklaceOriginalOuterHomIso_hom (T : NecklaceCode) :
    (necklaceOriginalOuterHomIso T).hom = (outerFlagIso T).hom ≫
      (chosenNecklaceIso T).inv.map (outerLeft T) (outerRight T) ≫
        targetHomTransport (necklaceInverseFirst T) (necklaceInverseLast T) := rfl

variable (X : SSet.{u}) (a b : X.obj (op ⦋0⦌))

/-- Exact κ: its apex and every leg are the original chosen C Hom and the original supplied map. -/
abbrev originalHomNecklaceCocone := chosenFlagHomCocone X a b

def originalHomNecklaceCoconeIso : flagCocone X a b ≅ originalHomNecklaceCocone X a b :=
  Cocones.ext (flagOriginalHomIso X a b) (fun P ↦ chosenFlagHom_leg P)

/-- Complete all-degree simplicial UP for that same original Hom cocone. -/
def originalHomNecklaceIsColimit : IsColimit (originalHomNecklaceCocone X a b) :=
  (flagIsColimit X a b).ofIsoColimit (originalHomNecklaceCoconeIso X a b)

def originalHomNecklaceDesc (s : Cocone (NecklacesOver.flagDiagram X a b)) :
    (RV X a ⟶[SSet.{u}] RV X b) ⟶ s.pt := (originalHomNecklaceIsColimit X a b).desc s

theorem originalHomNecklaceDesc_formula (s : Cocone (NecklacesOver.flagDiagram X a b)) :
    originalHomNecklaceDesc X a b s = (flagOriginalHomIso X a b).inv ≫ flagDesc X a b s := rfl

theorem originalHomNecklaceDesc_fac (s : Cocone (NecklacesOver.flagDiagram X a b))
    (P : NecklacesOver X a b) :
    chosenFlagLeg P ≫ originalHomNecklaceDesc X a b s = s.ι.app P :=
  (originalHomNecklaceIsColimit X a b).fac s P

theorem originalHomNecklaceDesc_uniq (s : Cocone (NecklacesOver.flagDiagram X a b))
    (k : (RV X a ⟶[SSet.{u}] RV X b) ⟶ s.pt) (hk : ∀ P, chosenFlagLeg P ≫ k = s.ι.app P) :
    k = originalHomNecklaceDesc X a b s := (originalHomNecklaceIsColimit X a b).uniq s k hk

def originalNecklaceFirst (P : NecklacesOver X a b) :
    (C.map P.map).obj (RV P.code.toSSet P.code.first) = RV X a :=
  (DaggerModels.OrdinaryRigidification.RigidificationVertices.vertexEquiv_naturality
    P.map P.code.first).trans (congrArg (RV X) P.first)

def originalNecklaceLast (P : NecklacesOver X a b) :
    (C.map P.map).obj (RV P.code.toSSet P.code.last) = RV X b :=
  (DaggerModels.OrdinaryRigidification.RigidificationVertices.vertexEquiv_naturality
    P.map P.code.last).trans (congrArg (RV X) P.last)

/-- All original map/endpoint data in κ are explicit; no replacement leg is selected. -/
theorem originalHomNecklace_leg (P : NecklacesOver X a b) :
    (originalHomNecklaceCocone X a b).ι.app P =
      (necklaceOriginalOuterHomIso P.code).hom ≫
        (C.map P.map).map (RV P.code.toSSet P.code.first) (RV P.code.toSSet P.code.last) ≫
          targetHomTransport (originalNecklaceFirst X a b P) (originalNecklaceLast X a b P) := by
  rw [necklaceOriginalOuterHomIso_hom]
  simp only [Category.assoc]
  rw [← Category.assoc (targetHomTransport (necklaceInverseFirst P.code)
    (necklaceInverseLast P.code)), enriched_map_endpoint_transport]
  simp only [Category.assoc]
  rw [targetHomTransport_trans]
  rfl

theorem originalHomNecklace_leg_naturality {P Q : NecklacesOver X a b} (h : P ⟶ Q) :
    flagMap h.hom ≫ (originalHomNecklaceCocone X a b).ι.app Q =
      (originalHomNecklaceCocone X a b).ι.app P := chosenFlagLeg_naturality h

theorem originalHomNecklace_postcomp {Y : SSet.{u}} (f : X ⟶ Y) (P : NecklacesOver X a b) :
    (originalHomNecklaceCocone X a b).ι.app P ≫ originalChosenHomMap f a b =
      (originalHomNecklaceCocone Y (f.app _ a) (f.app _ b)).ι.app
        ((NecklacesOver.postcomp f).obj P) := (chosenFlagLeg_postcomp f P).symm

/-- The original terminal interval leg, rather than id:T→T at unrelated endpoints. -/
def intervalOriginalHomLegIso (T : NecklaceCode) (x y : Fin (T.len + 1)) (hxy : x ≤ y) :
    flagSSet.{u} (intervalCode T x y hxy) ≅
      (RV T.toSSet (T.verticesEquiv.symm (ULift.up x)) ⟶[SSet.{u}]
        RV T.toSSet (T.verticesEquiv.symm (ULift.up y))) :=
  intervalFlagLegIso T x y hxy ≪≫ flagOriginalHomIso T.toSSet _ _

theorem intervalOriginalHomLegIso_hom (T : NecklaceCode)
    (x y : Fin (T.len + 1)) (hxy : x ≤ y) :
    (intervalOriginalHomLegIso T x y hxy).hom =
      chosenFlagLeg (intervalOver.{u} T x y hxy) := rfl

theorem intervalOriginalHomLegIso_diagonal_code (T : NecklaceCode)
    (x : Fin (T.len + 1)) : intervalCode T x x le_rfl = point := intervalCode_diagonal T x

/-- All reversed endpoint degrees of the same original C Hom are empty. -/
def originalReverseHomIsEmpty (T : NecklaceCode) (x y : Fin (T.len + 1)) (hxy : ¬x ≤ y)
    (q : SimplexCategoryᵒᵖ) : IsEmpty
      ((RV T.toSSet (T.verticesEquiv.symm (ULift.up x)) ⟶[SSet.{u}]
        RV T.toSSet (T.verticesEquiv.symm (ULift.up y))).obj q) := by
  refine ⟨fun p ↦ ?_⟩
  let t := (flagOriginalHomIso T.toSSet (T.verticesEquiv.symm (ULift.up x))
    (T.verticesEquiv.symm (ULift.up y))).inv.app q p
  induction t using Quot.ind with | _ r
  exact hxy (over_endpoints_le T x y r.1)

end

end DaggerChosenRigidificationNecklace
