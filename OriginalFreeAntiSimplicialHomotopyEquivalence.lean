import NativeReversedSimplicialHomotopy
import OriginalAntiInvolutiveFreePairMono

/-!
# The actual free anti-involutive map retains a supplied two-direction contraction

Both original homotopy directions are explicit. The second simplex copy uses
native reversal of the parameter and hence the opposite original homotopy.
The final map is the literal original tagged free left adjoint, via its existing
natural two-copy comparison. No model structure on anti-involutive sets is used.
-/
set_option autoImplicit false
open CategoryTheory Simplicial Opposite MonoidalCategory DaggerModels
open OriginalAntiInvolutiveFreePair OriginalTaggedReverseFreeCompletion
open DaggerNativeReversedSimplicialHomotopy
universe u
namespace DaggerOriginalFreeAntiSimplicialHomotopyEquivalence
noncomputable section

/-- Use the original cylinder on the first copy and the reversed opposite one on the second. -/
def pairCylinder {A B : SSet.{u}} {f g : A ⟶ B}
    (h : SSet.Homotopy f g) (k : SSet.Homotopy g f) : pairSSet A ⊗ Δ[1] ⟶ pairSSet B where
  app n p := if p.1.2 then ((reversedCylinder k).app n (p.1.1, p.2), true)
    else (h.h.app n (p.1.1, p.2), false)
  naturality n m i := by
    funext p
    rcases p with ⟨⟨x, b⟩, t⟩
    cases b
    · change (h.h.app m (A.map i x, Δ[1].map i t), false) =
        (B.map i (h.h.app n (x, t)), false)
      exact Prod.ext (congrFun (h.h.naturality i) (x, t)) rfl
    · change ((reversedCylinder k).app m (A.op.map i x, Δ[1].map i t), true) =
        (B.op.map i ((reversedCylinder k).app n (x, t)), true)
      exact Prod.ext (congrFun ((reversedCylinder k).naturality i) (x, t)) rfl

/-- The full two-copy cylinder joins the original two full pair maps. -/
def pairHomotopy {A B : SSet.{u}} {f g : A ⟶ B}
    (h : SSet.Homotopy f g) (k : SSet.Homotopy g f) :
    SSet.Homotopy (pairMap f).hom (pairMap g).hom :=
  SSet.Homotopy.mk (pairCylinder h k) (by
    ext n p
    rcases p with ⟨x, b⟩
    cases b
    · exact Prod.ext (congrFun (NatTrans.congr_app h.h₀ n) x) rfl
    · exact Prod.ext (congrFun (NatTrans.congr_app (reversedHomotopy k).h₀ n) x) rfl) (by
    ext n p
    rcases p with ⟨x, b⟩
    cases b
    · exact Prod.ext (congrFun (NatTrans.congr_app h.h₁ n) x) rfl
    · exact Prod.ext (congrFun (NatTrans.congr_app (reversedHomotopy k).h₁ n) x) rfl)

/-- The whole two-copy map is a raw homotopy equivalence with these exact inverse inputs. -/
def pairHomotopyEquiv {A B : SSet.{u}} (e : SSet.HomotopyEquiv A B)
    (kA : SSet.Homotopy (𝟙 A) (e.hom ≫ e.inv))
    (kB : SSet.Homotopy (𝟙 B) (e.inv ≫ e.hom)) :
    SSet.HomotopyEquiv (pairSSet A) (pairSSet B) where
  hom := (pairMap e.hom).hom
  inv := (pairMap e.inv).hom
  homInvId := pairHomotopy e.homInvId kA
  invHomId := pairHomotopy e.invHomId kB

/-- The existing free-adjoint uniqueness isomorphism on the actual underlying simplicial sets. -/
def underlyingPairIso (A : SSet.{u}) : pairSSet A ≅ (freeAnti.obj A).toSSet :=
  antiForget.mapIso (pairIsoFreeAnti.app A)

/-- Carry the whole supplied pair equivalence to the literal original free anti objects. -/
def freeAntiHomotopyEquiv {A B : SSet.{u}} (e : SSet.HomotopyEquiv A B)
    (kA : SSet.Homotopy (𝟙 A) (e.hom ≫ e.inv))
    (kB : SSet.Homotopy (𝟙 B) (e.inv ≫ e.hom)) :
    SSet.HomotopyEquiv (freeAnti.obj A).toSSet (freeAnti.obj B).toSSet := by
  let p := pairHomotopyEquiv e kA kB
  let a := underlyingPairIso A
  let b := underlyingPairIso B
  refine
    { hom := a.inv ≫ p.hom ≫ b.hom
      inv := b.inv ≫ p.inv ≫ a.hom
      homInvId := ?_
      invHomId := ?_ }
  · exact ((p.homInvId.precomp a.inv).postcomp a.hom).congr
      (by simp [Category.assoc]) (by simp)
  · exact ((p.invHomId.precomp b.inv).postcomp b.hom).congr
      (by simp [Category.assoc]) (by simp)

/-- Its forward map is exactly the original free anti map, with both endpoints retained. -/
theorem freeAntiHomotopyEquiv_hom {A B : SSet.{u}} (e : SSet.HomotopyEquiv A B)
    (kA : SSet.Homotopy (𝟙 A) (e.hom ≫ e.inv))
    (kB : SSet.Homotopy (𝟙 B) (e.inv ≫ e.hom)) :
    (freeAntiHomotopyEquiv e kA kB).hom = (freeAnti.map e.hom).hom := by
  change (underlyingPairIso A).inv ≫ (pairMap e.hom).hom ≫ (underlyingPairIso B).hom = _
  have hn : (pairMap e.hom).hom ≫ (underlyingPairIso B).hom =
      (underlyingPairIso A).hom ≫ (freeAnti.map e.hom).hom :=
    congrArg AntiInvolutiveSSet.Hom.hom (pairIsoFreeAnti.hom.naturality e.hom)
  rw [hn, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

end
end DaggerOriginalFreeAntiSimplicialHomotopyEquivalence
