import ChosenNecklaceTargetJoints
import ChosenFlagHomColimit
import ChosenNecklaceEnrichment

open CategoryTheory Limits Opposite Simplicial

universe u

namespace DaggerChosenRigidificationNecklace

noncomputable section

open NecklaceCode NecklaceThickening

variable (T : NecklaceCode) {x y : (toSSet.{u} T).obj (op ⦋0⦌)}
  (P : NecklacesOver (toSSet.{u} T) x y)

theorem over_map_vertices_first : mapVertices P.map (ULift.up 0) = T.verticesEquiv x := by
  change T.verticesEquiv (P.map.app _ P.code.first) = _
  rw [P.first]

theorem over_map_vertices_last :
    mapVertices P.map (ULift.up (Fin.last P.code.len)) = T.verticesEquiv y := by
  change T.verticesEquiv (P.map.app _ P.code.last) = _
  rw [P.last]

/-- The actual image of each unflanked set, retaining all original interior target joints. -/
def overFlagPath {n : ℕ} (F : NecklaceCode.Flag.{u} P.code n) (i : Fin (n + 1)) :
    JointPath (T.verticesEquiv x) (T.verticesEquiv y) where
  I := mapVertices P.map '' F.chain i
  left := ⟨ULift.up 0, F.chain.monotone (Fin.zero_le i) (F.joints _ P.code.first_mem),
    over_map_vertices_first T P⟩
  right := ⟨ULift.up (Fin.last P.code.len),
    F.chain.monotone (Fin.zero_le i) (F.joints _ P.code.last_mem),
    over_map_vertices_last T P⟩
  left_le v hv := by
    obtain ⟨k, hk, rfl⟩ := hv
    have h := (orderMap P.map).monotone (Fin.zero_le k.down)
    have he := congrArg ULift.down (over_map_vertices_first T P)
    change (orderMap P.map) 0 = (T.verticesEquiv x).down at he
    change (T.verticesEquiv x).down ≤ (mapVertices P.map k).down
    rw [← he]
    exact h
  le_right v hv := by
    obtain ⟨k, hk, rfl⟩ := hv
    have h := (orderMap P.map).monotone (Fin.le_last k.down)
    have he := congrArg ULift.down (over_map_vertices_last T P)
    change (orderMap P.map) (Fin.last P.code.len) = (T.verticesEquiv y).down at he
    change (mapVertices P.map k).down ≤ (T.verticesEquiv y).down
    rw [← he]
    exact h
  joints j hj hl hr := by
    obtain ⟨k, hk, he⟩ := original_over_target_joint P j hj hl hr
    exact ⟨ULift.up k, F.chain.monotone (Fin.zero_le i) (F.joints _ hk),
      ULift.ext _ _ he⟩

def overFlagNerve {n : ℕ} (F : NecklaceCode.Flag.{u} P.code n) :
    (nerve (JointPath (T.verticesEquiv x) (T.verticesEquiv y))).obj (op ⦋n⦌) where
  obj := overFlagPath T P F
  map h := ⟨⟨⟨Set.image_mono (F.chain.monotone (leOfHom h))⟩⟩⟩

theorem overFlagNerve_relation (Q : NecklacesOver (toSSet.{u} T) x y) (h : P ⟶ Q)
    {n : ℕ} (F : NecklaceCode.Flag.{u} P.code n) :
    overFlagNerve T Q (NecklaceCode.Flag.map h.hom F) = overFlagNerve T P F := by
  exact CategoryTheory.Functor.ext (fun i ↦ JointPath.ext (by
    change mapVertices Q.map '' (mapVertices h.hom.map '' F.chain i) =
      mapVertices P.map '' F.chain i
    rw [Set.image_image]
    change (mapVertices Q.map ∘ mapVertices h.hom.map) '' F.chain i = _
    rw [← mapVertices_comp, h.w]))

/-- Evaluate the SAME full original flag quotient by the actual image-of-vertices formula. -/
def necklaceFlagEvaluation : flagHom (toSSet.{u} T) x y ⟶
    nerve (JointPath (T.verticesEquiv x) (T.verticesEquiv y)) where
  app q := Quot.lift (fun p ↦ overFlagNerve T p.1 p.2) (by
    rintro ⟨P, F⟩ ⟨Q, G⟩ ⟨h, he⟩
    change G = NecklaceCode.Flag.map h.hom F at he
    rw [he]
    exact (overFlagNerve_relation T P Q h F).symm)
  naturality p q α := by
    funext v
    induction v using Quot.ind with | _ r
    exact CategoryTheory.Functor.ext (fun _ ↦ JointPath.ext rfl)

theorem necklaceFlagEvaluation_raw {n : ℕ} (F : NecklaceCode.Flag.{u} P.code n)
    (i : Fin (n + 1)) :
    (((necklaceFlagEvaluation T).app _ (Quot.mk _ ⟨P, F⟩)).obj i).I =
      mapVertices P.map '' F.chain i := rfl

end

end DaggerChosenRigidificationNecklace
