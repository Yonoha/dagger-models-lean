import DaggerModels.FreeBoundary

/-!
# Transporting actual free boundary-cell presentations

The generators from any two left adjoints of the same forgetful functor are
naturally isomorphic. This transports cell-attachment data while retaining
the original stage map. A countable relative cell presentation also belongs
to the stated saturation in the arbitrary simplex universe.
-/

open CategoryTheory Limits Simplicial HomotopicalAlgebra

universe u

namespace DaggerModels

/-- Transfer the actual boundary attachments between two choices of the free adjunction. -/
noncomputable def boundaryAttachmentOfAdjunction
    (F G : SSet.{u} ⥤ DaggerSSet.{u})
    (adjF : F ⊣ DaggerSSet.forget) (adjG : G ⊣ DaggerSSet.forget)
    {X Y : DaggerSSet.{u}} {f : X ⟶ Y}
    (c : AttachCells.{u} (fun n : ℕ ↦ F.map (SSet.boundary.{u} n).ι) f) :
    AttachCells.{u} (fun n : ℕ ↦ G.map (SSet.boundary.{u} n).ι) f := by
  let e := Adjunction.leftAdjointUniq adjF adjG
  exact c.reindexCellTypes (fun n : ℕ ↦ G.map (SSet.boundary.{u} n).ι) id
    (fun n ↦ Arrow.isoMk' _ _ (e.app _) (e.app _)
      (e.hom.naturality (SSet.boundary.{u} n).ι).symm)

/-- Countable actual relative boundary cells lie in the saturation at every value universe. -/
theorem freeBoundarySaturation_of_relativeCellComplexNat
    (F : SSet.{u} ⥤ DaggerSSet.{u}) {X Y : DaggerSSet.{u}} {f : X ⟶ Y}
    (c : RelativeCellComplex.{u}
      (fun (_ : ℕ) ↦ fun n : ℕ ↦ F.map (SSet.boundary.{u} n).ι) f) :
    (MorphismProperty.transfiniteCompositions.{u}
      (MorphismProperty.coproducts.{u} (freeBoundaryGenerators F)).pushouts).retracts f := by
  let : SuccOrder (ULift.{u} ℕ) := SuccOrder.ofOrderIso ULift.orderIso.symm
  have h := c.transfiniteCompositionOfShape (fun n : ℕ ↦ F.map (SSet.boundary.{u} n).ι)
  have h' := h.ofOrderIso (ULift.orderIso : ULift.{u} ℕ ≃o ℕ)
  apply MorphismProperty.le_retracts
  rw [MorphismProperty.transfiniteCompositions_iff]
  exact ⟨ULift.{u} ℕ, inferInstance, inferInstance, inferInstance, inferInstance, ⟨h'⟩⟩

end DaggerModels
