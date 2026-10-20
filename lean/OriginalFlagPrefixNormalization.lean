import OriginalFlagNormalizedBeads
import ChosenNecklaceWedgeDegree

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial

universe u

namespace DaggerOriginalFlagFlankification

noncomputable section

open DaggerChosenRigidificationNecklace NecklaceCode

variable {X : SSet.{u}} {a b : X.obj (op ⦋0⦌)}

theorem wedgeMap_vertex_surjective {T U T' U' : NecklaceCode}
    (f : NecklaceCode.Hom.{u} T T') (g : NecklaceCode.Hom.{u} U U')
    (hf : Function.Surjective (mapVertices f.map))
    (hg : Function.Surjective (mapVertices g.map)) :
    Function.Surjective (mapVertices (wedgeMap f g).map) := by
  intro z
  rcases wedge_degree_cover T' U' ((wedge T' U').verticesEquiv.symm z) with
    ⟨y, hy⟩ | ⟨y, hy⟩
  · obtain ⟨v, hv⟩ := hf (T'.verticesEquiv y)
    refine ⟨mapVertices (wedgeιLeft T U) v, ?_⟩
    have h := congrArg mapVertices (wedgeMap_left f g)
    rw [mapVertices_comp, mapVertices_comp] at h
    calc
      mapVertices (wedgeMap f g).map (mapVertices (wedgeιLeft T U) v) =
          mapVertices (wedgeιLeft T' U') (mapVertices f.map v) := congrFun h v
      _ = mapVertices (wedgeιLeft T' U') (T'.verticesEquiv y) := congrArg _ hv
      _ = z := by
        dsimp only [mapVertices]
        rw [T'.verticesEquiv.symm_apply_apply, hy,
          (wedge T' U').verticesEquiv.apply_symm_apply]
  · obtain ⟨v, hv⟩ := hg (U'.verticesEquiv y)
    refine ⟨mapVertices (wedgeιRight T U) v, ?_⟩
    have h := congrArg mapVertices (wedgeMap_right f g)
    rw [mapVertices_comp, mapVertices_comp] at h
    calc
      mapVertices (wedgeMap f g).map (mapVertices (wedgeιRight T U) v) =
          mapVertices (wedgeιRight T' U') (mapVertices g.map v) := congrFun h v
      _ = mapVertices (wedgeιRight T' U') (U'.verticesEquiv y) := congrArg _ hv
      _ = z := by
        dsimp only [mapVertices]
        rw [U'.verticesEquiv.symm_apply_apply, hy,
          (wedge T' U').verticesEquiv.apply_symm_apply]

def jointVertex (P : NecklacesOver X a b) (i : Fin (beadCount P.code + 1)) :
    X.obj (op ⦋0⦌) := vertexImage P (jointEmbedding P.code i)

theorem jointVertex_first (P : NecklacesOver X a b) : jointVertex P 0 = a := by
  rw [jointVertex, jointEmbedding_first, vertexImage_first]

theorem jointVertex_last (P : NecklacesOver X a b) :
    jointVertex P (Fin.last (beadCount P.code)) = b := by
  rw [jointVertex, jointEmbedding_last, vertexImage_last]

/-- Every prefix retains its original last joint, even when its image repeats the first. -/
structure PrefixNormalizationData (P : NecklacesOver X a b) (k : ℕ)
    (hk : k ≤ beadCount P.code) where
  source : NecklacesOver X (jointVertex P 0) (jointVertex P ⟨k, Nat.lt_succ_of_le hk⟩)
  normalized : NecklacesOver X (jointVertex P 0)
    (jointVertex P ⟨k, Nat.lt_succ_of_le hk⟩)
  ν : source ⟶ normalized

/-- Finite fold of the ACTUAL original beads and ACTUAL chosen EZ decompositions in order. -/
def orderedPrefix (P : NecklacesOver X a b) :
    (k : ℕ) → (hk : k ≤ beadCount P.code) → PrefixNormalizationData P k hk
  | 0, _ =>
      { source := NecklacesOver.point (jointVertex P 0)
        normalized := NecklacesOver.point (jointVertex P 0)
        ν := 𝟙 _ }
  | k + 1, hk =>
      let hp : k ≤ beadCount P.code := Nat.le_of_succ_le hk
      let prev := orderedPrefix P k hp
      let i : Fin (beadCount P.code) := ⟨k, lt_of_lt_of_le (Nat.lt_succ_self k) hk⟩
      let c := jointBead P.code i
      let d := normalizeBead P c
      { source := NecklacesOver.wedge prev.source (sourceBeadOver P c)
        normalized := NecklacesOver.wedge prev.normalized (normalizedBeadOver P c d)
        ν := NecklacesOver.wedgeHom prev.ν (normalizedBeadHom P c d) }

theorem orderedPrefix_triangle (P : NecklacesOver X a b) (k : ℕ)
    (hk : k ≤ beadCount P.code) :
    (orderedPrefix P k hk).ν.hom.map ≫ (orderedPrefix P k hk).normalized.map =
      (orderedPrefix P k hk).source.map := (orderedPrefix P k hk).ν.w

theorem orderedPrefix_first (P : NecklacesOver X a b) (k : ℕ)
    (hk : k ≤ beadCount P.code) :
    (orderedPrefix P k hk).ν.hom.map.app _ (orderedPrefix P k hk).source.code.first =
      (orderedPrefix P k hk).normalized.code.first := (orderedPrefix P k hk).ν.hom.first

theorem orderedPrefix_last (P : NecklacesOver X a b) (k : ℕ)
    (hk : k ≤ beadCount P.code) :
    (orderedPrefix P k hk).ν.hom.map.app _ (orderedPrefix P k hk).source.code.last =
      (orderedPrefix P k hk).normalized.code.last := (orderedPrefix P k hk).ν.hom.last

theorem orderedPrefix_surjective (P : NecklacesOver X a b) (k : ℕ)
    (hk : k ≤ beadCount P.code) :
    Function.Surjective (mapVertices (orderedPrefix P k hk).ν.hom.map) := by
  induction k with
  | zero =>
    change Function.Surjective (mapVertices (𝟙 _))
    rw [mapVertices_id]
    exact Function.surjective_id
  | succ k ih =>
    dsimp only [orderedPrefix]
    exact wedgeMap_vertex_surjective _ _ (ih _) (normalizedBeadHom_surjective _ _ _)

/-- This recursive square retains every earlier bead leg; the second retains the new one. -/
theorem orderedPrefix_left_square (P : NecklacesOver X a b) (k : ℕ)
    (hk : k + 1 ≤ beadCount P.code) :
    let hp := Nat.le_of_succ_le hk
    let c := jointBead P.code ⟨k, lt_of_lt_of_le (Nat.lt_succ_self k) hk⟩
    let d := normalizeBead P c
    wedgeιLeft (orderedPrefix P k hp).source.code (sourceBeadOver P c).code ≫
        (orderedPrefix P (k + 1) hk).ν.hom.map =
      (orderedPrefix P k hp).ν.hom.map ≫
        wedgeιLeft (orderedPrefix P k hp).normalized.code (normalizedBeadOver P c d).code :=
  wedgeMap_left _ _

theorem orderedPrefix_right_square (P : NecklacesOver X a b) (k : ℕ)
    (hk : k + 1 ≤ beadCount P.code) :
    let hp := Nat.le_of_succ_le hk
    let c := jointBead P.code ⟨k, lt_of_lt_of_le (Nat.lt_succ_self k) hk⟩
    let d := normalizeBead P c
    wedgeιRight (orderedPrefix P k hp).source.code (sourceBeadOver P c).code ≫
        (orderedPrefix P (k + 1) hk).ν.hom.map =
      (normalizedBeadHom P c d).hom.map ≫
        wedgeιRight (orderedPrefix P k hp).normalized.code (normalizedBeadOver P c d).code :=
  wedgeMap_right _ _

theorem orderedPrefix_operator (P : NecklacesOver X a b) (k : ℕ)
    (hk : k ≤ beadCount P.code) {p q : SimplexCategoryᵒᵖ} (α : p ⟶ q) :
    (orderedPrefix P k hk).source.code.toSSet.map α ≫
        (orderedPrefix P k hk).ν.hom.map.app q =
      (orderedPrefix P k hk).ν.hom.map.app p ≫
        (orderedPrefix P k hk).normalized.code.toSSet.map α :=
  (orderedPrefix P k hk).ν.hom.map.naturality α

end

end DaggerOriginalFlagFlankification
