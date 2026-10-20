import OriginalFlagDegree
import ChosenNecklaceBeadCoordinates
import Mathlib.AlgebraicTopology.SimplicialSet.Degenerate

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial

universe u

namespace DaggerOriginalFlagFlankification

noncomputable section

open DaggerChosenRigidificationNecklace NecklaceCode

variable {X : SSet.{u}} {a b : X.obj (op ⦋0⦌)}

def beadElement (P : NecklacesOver X a b) (c : P.code.Bead) : X _⦋c.length⦌ :=
  SSet.yonedaEquiv (P.code.beadSimplex c ≫ P.map)

/-- The original Eilenberg-Zilber decomposition, including an actual dimension-zero collapse. -/
structure NondegenerateBeadData (P : NecklacesOver X a b) (c : P.code.Bead) where
  dim : ℕ
  operator : ⦋c.length⦌ ⟶ ⦋dim⦌
  epi : Epi operator
  simplex : X.nonDegenerate dim
  fac : beadElement P c = X.map operator.op simplex.val

def normalizeBead (P : NecklacesOver X a b) (c : P.code.Bead) :
    NondegenerateBeadData P c :=
  Classical.choice (show Nonempty (NondegenerateBeadData P c) from by
    obtain ⟨m, f, hf, x, hx⟩ := X.exists_nonDegenerate (beadElement P c)
    exact ⟨⟨m, f, hf, x, hx⟩⟩)

theorem beadNormalization_triangle (P : NecklacesOver X a b) (c : P.code.Bead)
    (d : NondegenerateBeadData P c) :
    SSet.stdSimplex.map d.operator ≫ SSet.yonedaEquiv.symm d.simplex.val =
      P.code.beadSimplex c ≫ P.map := by
  apply SSet.yonedaEquiv.injective
  rw [SSet.yonedaEquiv_comp, SSet.stdSimplex.yonedaEquiv_map]
  change X.map d.operator.op d.simplex.val = beadElement P c
  exact d.fac.symm

/-- Equal original bead maps have the same nondegenerate dimension, without Mono into X. -/
theorem beadNormalization_dim_unique (P : NecklacesOver X a b) (c : P.code.Bead)
    (d e : NondegenerateBeadData P c) : d.dim = e.dim := by
  letI := d.epi
  letI := e.epi
  exact X.unique_nonDegenerate_dim (beadElement P c) d.operator d.simplex d.fac
    e.operator e.simplex e.fac

end

end DaggerOriginalFlagFlankification
