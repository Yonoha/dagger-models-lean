import OriginalPathContraction
import IntervalCompletionEndpoints
import ChosenNecklaceOuterFlags
import ChosenNecklaceSingleThickening

set_option autoImplicit false

open CategoryTheory MonoidalCategory Opposite Simplicial

universe u

namespace DaggerOriginalIntervalFlagContraction

noncomputable section

open DaggerChosenRigidificationNecklace NecklaceCode NecklaceThickening

abbrev firstVertex (N : ℕ) : Vertices.{u} (single N) := ULift.up 0
abbrev lastVertex (N : ℕ) : Vertices.{u} (single N) := ULift.up (Fin.last N)

/-- The two accepted original isos; no new path category is introduced. -/
def singleFlagPathIso (N : ℕ) :
    flagSSet.{u} (single N) ≅
      DaggerOriginalPathContraction.pathNerve (firstVertex N) (lastVertex N) :=
  outerFlagIso (single N) ≪≫ singlePathIso N (firstVertex N) (lastVertex N)

def bottomFlag (N n : ℕ) : NecklaceCode.Flag.{u} (single N) n where
  chain := OrderHom.const _ {firstVertex N, lastVertex N}
  joints v hv := by
    rcases (mem_single_joints N v.down).mp hv with h | h
    · left; exact ULift.ext _ _ h
    · right; exact ULift.ext _ _ h

def singleHomotopyMap (N : ℕ) : flagSSet.{u} (single N) ⊗ Δ[1] ⟶
    flagSSet.{u} (single N) :=
  ((singleFlagPathIso N).hom ⊗ₘ 𝟙 _) ≫
    (DaggerOriginalPathContraction.contraction (firstVertex N) (lastVertex N)
      (show firstVertex N ≤ lastVertex N from Fin.zero_le _)).h ≫
    (singleFlagPathIso N).inv

def squeezeFlag (N : ℕ) (q : SimplexCategoryᵒᵖ)
    (F : NecklaceCode.Flag.{u} (single N) q.unop.len) (t : (Δ[1] : SSet.{u}).obj q) :
    NecklaceCode.Flag.{u} (single N) q.unop.len := (singleHomotopyMap N).app q (F, t)

/-- This is the exact I0 all-time formula transported through the existing two isos. -/
theorem squeezeFlag_chain (N : ℕ) (q : SimplexCategoryᵒᵖ)
    (F : NecklaceCode.Flag.{u} (single N) q.unop.len) (t : (Δ[1] : SSet.{u}).obj q)
    (i : Fin (q.unop.len + 1)) :
    (squeezeFlag N q F t).chain i =
      if (SSet.stdSimplex.objEquiv t).toOrderHom i = 0 then
        {firstVertex N, lastVertex N} else F.chain i := by
  exact DaggerOriginalPathContraction.contraction_obj_I
    (firstVertex N) (lastVertex N) (Fin.zero_le _) q
    ((singleFlagPathIso N).hom.app q F) t i

theorem squeezeFlag_operator (N : ℕ) {q r : SimplexCategoryᵒᵖ} (α : q ⟶ r)
    (F : NecklaceCode.Flag.{u} (single N) q.unop.len) (t : (Δ[1] : SSet.{u}).obj q) :
    NecklaceCode.Flag.restrict α.unop.toOrderHom (squeezeFlag N q F t) =
      squeezeFlag N r (NecklaceCode.Flag.restrict α.unop.toOrderHom F)
        ((Δ[1] : SSet.{u}).map α t) :=
  (congrFun ((singleHomotopyMap N).naturality α) (F, t)).symm

/-- Exact I0 naturality, with the actual images of BOTH endpoints still visible. -/
theorem original_path_naturality {N M : ℕ} (f : Hom.{u} (single N) (single M)) :
    (nerveMap (SimplicialThickening.functorMap (vertexOrderMap f)
        (.mk (firstVertex N)) (.mk (lastVertex N))) ⊗ₘ 𝟙 (Δ[1] : SSet.{u})) ≫
      (DaggerOriginalPathContraction.contraction
        (vertexOrderMap f (firstVertex N)) (vertexOrderMap f (lastVertex N))
        ((vertexOrderMap f).monotone (Fin.zero_le _))).h =
    (DaggerOriginalPathContraction.contraction (firstVertex N) (lastVertex N)
      (Fin.zero_le _)).h ≫
      nerveMap (SimplicialThickening.functorMap (vertexOrderMap f)
        (.mk (firstVertex N)) (.mk (lastVertex N))) :=
  DaggerOriginalPathContraction.contraction_natural _ _ _ _

theorem squeezeFlag_map {N M : ℕ} (f : Hom.{u} (single N) (single M))
    (q : SimplexCategoryᵒᵖ) (F : NecklaceCode.Flag.{u} (single N) q.unop.len)
    (t : (Δ[1] : SSet.{u}).obj q) :
    NecklaceCode.Flag.map f (squeezeFlag N q F t) =
      squeezeFlag M q (NecklaceCode.Flag.map f F) t := by
  have hf : mapVertices f.map (firstVertex N) = firstVertex M := by
    apply ULift.ext
    exact orderMap_first f
  have hl : mapVertices f.map (lastVertex N) = lastVertex M := by
    apply ULift.ext
    exact orderMap_last f
  apply NecklaceCode.Flag.ext
  intro i
  change mapVertices f.map '' (squeezeFlag N q F t).chain i = _
  rw [squeezeFlag_chain, squeezeFlag_chain]
  split_ifs
  · rw [Set.image_insert_eq, Set.image_singleton, hf, hl]
  · rfl

theorem singleHomotopy_naturality {N M : ℕ} (f : Hom.{u} (single N) (single M)) :
    (flagMap f ⊗ₘ 𝟙 (Δ[1] : SSet.{u})) ≫ singleHomotopyMap M =
      singleHomotopyMap N ≫ flagMap f := by
  ext q x
  exact (squeezeFlag_map f q x.1 x.2).symm

theorem singleHomotopy_zero (N : ℕ) :
    SSet.ι₀ ≫ singleHomotopyMap.{u} N = SSet.const (bottomFlag N 0) := by
  ext q F
  apply NecklaceCode.Flag.ext
  intro i
  change (squeezeFlag N q F (SSet.ι₀.app q F).2).chain i = _
  rw [squeezeFlag_chain]
  simp [bottomFlag, SSet.ι₀, SSet.const, SSet.stdSimplex.const]
  rfl

theorem singleHomotopy_one (N : ℕ) :
    SSet.ι₁ ≫ singleHomotopyMap.{u} N = 𝟙 (flagSSet (single N)) := by
  ext q F
  apply NecklaceCode.Flag.ext
  intro i
  change (squeezeFlag N q F (SSet.ι₁.app q F).2).chain i = _
  rw [squeezeFlag_chain]
  simp [SSet.ι₁, SSet.const, SSet.stdSimplex.const]

end

end DaggerOriginalIntervalFlagContraction
