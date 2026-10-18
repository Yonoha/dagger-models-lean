import OriginalProductCutRefinement
import OriginalFlagBeadNormalizationLaws

set_option autoImplicit false
open CategoryTheory Limits Opposite Simplicial
open DaggerChosenRigidificationNecklace
open DaggerChosenRigidificationNecklace.NecklaceCode
open DaggerOriginalFlagFlankification

universe u

namespace DaggerOriginalProductGadget

noncomputable section

variable {X Y : SSet.{u}} {a b : X.obj (op ⦋0⦌)} {q r : SimplexCategoryᵒᵖ}

/-- The actual images of the vertices in the first set of the supplied original flag. -/
def rawFlagVertexSupport (p : RawFlag X a b q) : Set (X.obj (op ⦋0⦌)) :=
  (fun v : Vertices.{u} p.1.code ↦ vertexImage p.1 v.down) '' p.2.chain 0

theorem rawFlagVertexSupport_map {P Q : NecklacesOver X a b} (g : NecklacesOver.Hom P Q)
    (F : Flag.{u} P.code q.unop.len) :
    rawFlagVertexSupport (⟨Q, NecklaceCode.Flag.map g.hom F⟩ : RawFlag X a b q) =
      rawFlagVertexSupport (⟨P, F⟩ : RawFlag X a b q) := by
  change (fun v : Vertices.{u} Q.code ↦ vertexImage Q v.down) ''
      (mapVertices g.hom.map '' F.chain 0) = _
  rw [Set.image_image]
  apply congrArg (fun f ↦ f '' F.chain 0)
  funext v
  change Q.map.app _ (Q.code.verticesEquiv.symm
      (Q.code.verticesEquiv (g.hom.map.app _ (P.code.verticesEquiv.symm v)))) =
    P.map.app _ (P.code.verticesEquiv.symm v)
  rw [Equiv.symm_apply_apply]
  exact congrFun (NatTrans.congr_app g.w _) _

/-- A support on the same original flag quotient, invariant under every generating arrow. -/
def flagVertexSupport (x : (flagHom X a b).obj q) : Set (X.obj (op ⦋0⦌)) :=
  Quot.lift rawFlagVertexSupport (by
    rintro ⟨P, F⟩ ⟨Q, G⟩ ⟨g, hg⟩
    change G = NecklaceCode.Flag.map g.hom F at hg
    rw [hg]
    exact (rawFlagVertexSupport_map g F).symm) x

theorem flagVertexSupport_mk (p : RawFlag X a b q) :
    flagVertexSupport (Quot.mk _ p) = rawFlagVertexSupport p := rfl

theorem flagVertexSupport_finite (x : (flagHom X a b).obj q) :
    (flagVertexSupport x).Finite := by
  induction x using Quot.ind with
  | _ p => exact (Set.toFinite (p.2.chain 0)).image _

theorem flagVertexSupport_first (x : (flagHom X a b).obj q) : a ∈ flagVertexSupport x := by
  induction x using Quot.ind with
  | _ p => exact ⟨ULift.up 0, p.2.joints _ p.1.code.first_mem, vertexImage_first p.1⟩

theorem flagVertexSupport_last (x : (flagHom X a b).obj q) : b ∈ flagVertexSupport x := by
  induction x using Quot.ind with
  | _ p =>
    exact ⟨ULift.up (Fin.last p.1.code.len), p.2.joints _ p.1.code.last_mem,
      vertexImage_last p.1⟩

/-- Simplicial operators can enlarge the first flag set, so gate membership is preserved. -/
theorem flagVertexSupport_operator (α : q ⟶ r) (x : (flagHom X a b).obj q) :
    flagVertexSupport x ⊆ flagVertexSupport ((flagHom X a b).map α x) := by
  induction x using Quot.ind with
  | _ p =>
    exact Set.image_mono (p.2.chain.monotone (Fin.zero_le (α.unop.toOrderHom 0)))

/-- Support is transported by the literal original postcomposition map. -/
theorem flagVertexSupport_postcomp (f : X ⟶ Y) (x : (flagHom X a b).obj q) :
    flagVertexSupport ((flagHomMap f).app q x) = f.app (op ⦋0⦌) '' flagVertexSupport x := by
  induction x using Quot.ind with
  | _ p =>
    change (fun v : Vertices.{u} p.1.code ↦ f.app _ (vertexImage p.1 v.down)) ''
      p.2.chain 0 = f.app _ '' ((fun v : Vertices.{u} p.1.code ↦ vertexImage p.1 v.down) ''
        p.2.chain 0)
    rw [Set.image_image]

end

end DaggerOriginalProductGadget
