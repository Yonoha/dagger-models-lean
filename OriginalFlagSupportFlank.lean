import OriginalFlagVertexSupport
import OriginalFlagFlankFunctor

set_option autoImplicit false
open CategoryTheory Limits Opposite Simplicial
open DaggerChosenRigidificationNecklace
open DaggerChosenRigidificationNecklace.NecklaceCode
open DaggerOriginalFlagFlankification

universe u

namespace DaggerOriginalProductGadget

noncomputable section

variable {X : SSet.{u}} {a b : X.obj (op ⦋0⦌)} {n : ℕ}

/-- Literal images of all actual source joints; no injectivity hypothesis is inserted. -/
def necklaceJointImage (P : NecklacesOver X a b) : Set (X.obj (op ⦋0⦌)) :=
  {x | ∃ v : Fin (P.code.len + 1), v ∈ P.code.joints ∧ vertexImage P v = x}

theorem flagVertexSupport_flanked (P : NecklacesOver X a b)
    (F : Flag.{u} P.code n) (hF : Flanked F) :
    flagVertexSupport (Quot.mk _ (⟨P, F⟩ : RawFlag X a b (op ⦋n⦌))) =
      necklaceJointImage P := by
  change (fun v : Vertices.{u} P.code ↦ vertexImage P v.down) '' F.chain 0 = _
  rw [hF.1]
  ext x
  constructor
  · rintro ⟨v, hv, he⟩
    exact ⟨v.down, hv, he⟩
  · rintro ⟨v, hv, he⟩
    exact ⟨ULift.up v, hv, he⟩

/-- The accepted flankification provides a representative whose actual joint image
is the entire support of the original quotient class. -/
theorem exists_flanked_support (x : (flagHom X a b).obj (op ⦋n⦌)) :
    ∃ (P : NecklacesOver X a b) (F : Flag.{u} P.code n),
      Flanked F ∧ Quot.mk _ (⟨P, F⟩ : RawFlag X a b (op ⦋n⦌)) = x ∧
        flagVertexSupport x = necklaceJointImage P := by
  induction x using Quot.ind with
  | _ p =>
    let p' := flankDegreeObj p
    have hF : Flanked p'.2 := flankification_flanked p
    have hx : Quot.mk _ (⟨p'.1, p'.2⟩ : RawFlag X a b (op ⦋n⦌)) = Quot.mk _ p :=
      flankification_class p
    exact ⟨p'.1, p'.2, hF, hx,
      (congrArg flagVertexSupport hx).symm.trans (flagVertexSupport_flanked p'.1 p'.2 hF)⟩

/-- Exact gate-image characterization using actual flanked representatives of the same quotient.
The additional ordered-target monomorphism condition is a separate obligation. -/
theorem gate_support_iff_flanked (S : Set (X.obj (op ⦋0⦌)))
    (x : (flagHom X a b).obj (op ⦋n⦌)) :
    S ⊆ flagVertexSupport x ↔
      ∃ (P : NecklacesOver X a b) (F : Flag.{u} P.code n),
        Flanked F ∧ Quot.mk _ (⟨P, F⟩ : RawFlag X a b (op ⦋n⦌)) = x ∧
          S ⊆ necklaceJointImage P := by
  constructor
  · intro hS
    obtain ⟨P, F, hF, hx, hs⟩ := exists_flanked_support x
    exact ⟨P, F, hF, hx, hs ▸ hS⟩
  · rintro ⟨P, F, hF, hx, hS⟩
    rw [← hx, flagVertexSupport_flanked P F hF]
    exact hS

end

end DaggerOriginalProductGadget
