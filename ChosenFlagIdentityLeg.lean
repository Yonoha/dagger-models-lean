import ChosenFlagFunctor
import ChosenEnrichedMapTransport

open CategoryTheory EnrichedCategory MonoidalCategory Opposite Simplicial

universe u

namespace DaggerChosenRigidificationNecklace

noncomputable section

open NecklaceCode

def identityOver (T : NecklaceCode) : NecklacesOver (toSSet.{u} T) T.first T.last where
  code := T
  map := 𝟙 _
  first := rfl
  last := rfl

def overEndpointTransport {X : SSet.{u}} {a b c d : X.obj (op ⦋0⦌)}
    (P : NecklacesOver X a b) (ha : a = c) (hb : b = d) : NecklacesOver X c d where
  code := P.code
  map := P.map
  first := P.first.trans ha
  last := P.last.trans hb

theorem flagHom_transport_raw {X : SSet.{u}} {a b c d : X.obj (op ⦋0⦌)}
    (P : NecklacesOver X a b) (ha : a = c) (hb : b = d)
    (q : SimplexCategoryᵒᵖ) (p : NecklaceCode.Flag.{u} P.code q.unop.len) :
    (targetHomTransport (D := E X) ha hb).app q (Quot.mk _ ⟨P, p⟩) =
      Quot.mk _ ⟨overEndpointTransport P ha hb, p⟩ := by
  cases ha
  cases hb
  rfl

theorem postcomp_identity_endpoint {X : SSet.{u}} {a b : X.obj (op ⦋0⦌)}
    (P : NecklacesOver X a b) :
    overEndpointTransport ((NecklacesOver.postcomp P.map).obj (identityOver P.code))
      P.first P.last = P := by
  cases P
  simp [overEndpointTransport, NecklacesOver.postcomp, identityOver]

/-- Each exact raw flag is the same original map applied to its identity-over-necklace flag. -/
theorem flagLeg_reproduction {X : SSet.{u}} {a b : X.obj (op ⦋0⦌)}
    (P : NecklacesOver X a b) :
    flagLeg P.code.toSSet P.code.first P.code.last (identityOver P.code) ≫
      (EMap P.map).map P.code.first P.code.last ≫ targetHomTransport P.first P.last =
        flagLeg X a b P := by
  ext q p
  change (targetHomTransport (D := E X) P.first P.last).app q (Quot.mk _
    ⟨(NecklacesOver.postcomp P.map).obj (identityOver P.code), p⟩) = _
  rw [flagHom_transport_raw]
  cases P
  rfl

end

end DaggerChosenRigidificationNecklace
