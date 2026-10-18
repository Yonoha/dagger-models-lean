import OriginalNecklaceIntervalRestriction
import OriginalNecklaceCutWedge

set_option autoImplicit false
open CategoryTheory Limits Opposite Simplicial
open DaggerChosenRigidificationNecklace
open DaggerChosenRigidificationNecklace.NecklaceCode

universe u

namespace DaggerOriginalProductGadget

noncomputable section

variable {S T : NecklaceCode} (f : toSSet.{u} S ⟶ toSSet.{u} T)

theorem necklaceMap_vertex_of_order (a : Fin (S.len + 1)) (c : Fin (T.len + 1))
    (h : orderMap f a = c) :
    f.app _ (S.verticesEquiv.symm (ULift.up a)) = T.verticesEquiv.symm (ULift.up c) := by
  apply T.verticesEquiv.injective
  rw [Equiv.apply_symm_apply]
  exact ULift.ext _ _ h

/-- Exact endpoint images upgrade the existing interval restriction to an original code arrow. -/
def intervalCodeHom (a b : Fin (S.len + 1)) (hab : a ≤ b)
    (c d : Fin (T.len + 1)) (hcd : c ≤ d)
    (hc : orderMap f a = c) (hd : orderMap f b = d) :
    NecklaceCode.Hom.{u} (intervalCode S a b hab) (intervalCode T c d hcd) where
  map := necklaceIntervalMap f a b hab c d hcd hc.ge hd.le
  first := by
    apply intervalι_injective T c d hcd
    calc
      (intervalι T c d hcd).app _
          ((necklaceIntervalMap f a b hab c d hcd hc.ge hd.le).app _
            (intervalCode S a b hab).first) =
          f.app _ ((intervalι S a b hab).app _ (intervalCode S a b hab).first) :=
        congrFun (NatTrans.congr_app
          (necklaceIntervalMap_fac f a b hab c d hcd hc.ge hd.le) _) _
      _ = T.verticesEquiv.symm (ULift.up c) := by
        rw [intervalι_first]
        exact necklaceMap_vertex_of_order f a c hc
      _ = (intervalι T c d hcd).app _ (intervalCode T c d hcd).first :=
        (intervalι_first T c d hcd).symm
  last := by
    apply intervalι_injective T c d hcd
    calc
      (intervalι T c d hcd).app _
          ((necklaceIntervalMap f a b hab c d hcd hc.ge hd.le).app _
            (intervalCode S a b hab).last) =
          f.app _ ((intervalι S a b hab).app _ (intervalCode S a b hab).last) :=
        congrFun (NatTrans.congr_app
          (necklaceIntervalMap_fac f a b hab c d hcd hc.ge hd.le) _) _
      _ = T.verticesEquiv.symm (ULift.up d) := by
        rw [intervalι_last]
        exact necklaceMap_vertex_of_order f b d hd
      _ = (intervalι T c d hcd).app _ (intervalCode T c d hcd).last :=
        (intervalι_last T c d hcd).symm

variable (g : NecklaceCode.Hom.{u} S T)
  (k : Fin (S.len + 1)) (l : Fin (T.len + 1)) (h : orderMap g.map k = l)

def cutLeftHom : NecklaceCode.Hom.{u} (cutLeft S k) (cutLeft T l) :=
  intervalCodeHom g.map 0 k (Fin.zero_le k) 0 l (Fin.zero_le l) (orderMap_first g) h

def cutRightHom : NecklaceCode.Hom.{u} (cutRight S k) (cutRight T l) :=
  intervalCodeHom g.map k (Fin.last S.len) (Fin.le_last k)
    l (Fin.last T.len) (Fin.le_last l) h (orderMap_last g)

theorem cutLeftHom_fac :
    (cutLeftHom g k l h).map ≫ cutLeftι T l = cutLeftι S k ≫ g.map :=
  necklaceIntervalMap_fac g.map 0 k (Fin.zero_le k) 0 l (Fin.zero_le l)
    (orderMap_first g).ge h.le

theorem cutRightHom_fac :
    (cutRightHom g k l h).map ≫ cutRightι T l = cutRightι S k ≫ g.map :=
  necklaceIntervalMap_fac g.map k (Fin.last S.len) (Fin.le_last k)
    l (Fin.last T.len) (Fin.le_last l) h.ge (orderMap_last g).le

end

end DaggerOriginalProductGadget
