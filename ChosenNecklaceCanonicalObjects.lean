import ChosenNecklaceSingleThickening
import ChosenNecklaceSliceIso

open CategoryTheory EnrichedCategory MonoidalCategory Opposite Simplicial

universe u

namespace DaggerChosenRigidificationNecklace

noncomputable section

open NecklaceCode NecklaceThickening

/-- The actual chosen-C object corresponds to the original necklace vertex. -/
def canonicalNCObject (T : NecklaceCode) (a : (C.{u}.obj T.toSSet).Obj) : (NC.{u} T).Obj :=
  ⟨T.verticesEquiv ((RV T.toSSet).symm a)⟩

theorem canonicalNCObject_vertex (T : NecklaceCode) (x : T.toSSet.obj (op ⦋0⦌)) :
    canonicalNCObject T (RV T.toSSet x) = ⟨T.verticesEquiv x⟩ := by
  simp only [canonicalNCObject, Equiv.symm_apply_apply]

/-- A whole comparison retains the canonical original object identification. -/
structure LabelledComparison (T : NecklaceCode) where
  iso : C.{u}.obj T.toSSet ≅ NC.{u} T
  objects : ∀ a, iso.hom.obj a = canonicalNCObject T a

theorem representable_hom_vertex (n : ℕ) (x : (Δ[n] : SSet.{u}).obj (op ⦋0⦌)) :
    (ρ.app ⦋n⦌).hom.obj (RV Δ[n] x) =
      DaggerModels.OrdinaryRigidification.RigidificationVertices.representableVerticesEquiv ⦋n⦌ x :=
  by
  rw [show RV Δ[n] x = (thickeningUnit.app ⦋n⦌).obj
    (DaggerModels.OrdinaryRigidification.RigidificationVertices.representableVerticesEquiv
      ⦋n⦌ x) from
    DaggerModels.OrdinaryRigidification.RigidificationVertices.canonicalVertex_simplex ⦋n⦌ x]
  exact congrArg (fun F ↦ F.obj
    (DaggerModels.OrdinaryRigidification.RigidificationVertices.representableVerticesEquiv
      ⦋n⦌ x)) (representable_unit_hom ⦋n⦌)

def singleChosenIso (n : ℕ) : C.{u}.obj (toSSet (single n)) ≅ NC.{u} (single n) :=
  C.mapIso (singleIso n) ≪≫ ρ.app ⦋n⦌ ≪≫ (singleNCIso n).symm

theorem singleChosenIso_vertex (n : ℕ) (x : (toSSet.{u} (single n)).obj (op ⦋0⦌)) :
    (singleChosenIso n).hom.obj (RV _ x) = ⟨(single n).verticesEquiv x⟩ := by
  change (singleNCIso n).inv.obj ((ρ.app ⦋n⦌).hom.obj
    ((C.map (singleIso n).hom).obj (RV _ x))) = _
  rw [DaggerModels.OrdinaryRigidification.RigidificationVertices.vertexEquiv_naturality,
    representable_hom_vertex]
  apply congrArg NecklaceThickening.mk
  apply ULift.ext
  exact singleIso_vertex n x

def singleComparison (n : ℕ) : LabelledComparison.{u} (single n) where
  iso := singleChosenIso n
  objects a := by
    obtain ⟨x, rfl⟩ := (RV (toSSet (single n))).surjective a
    rw [canonicalNCObject_vertex]
    exact singleChosenIso_vertex n x

end

end DaggerChosenRigidificationNecklace
