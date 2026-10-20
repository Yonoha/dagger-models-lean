import ChallengeActualQKanCotensorWeakness
import ActualQKanCotensorComparison
import ActualKanSimplexCotensorComparison
import ProofActualRightConeSingularComparison

set_option autoImplicit false
universe u
namespace DaggerActualQKanCotensorWeaknessChallenge

theorem verified : statement.{u} := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro X Y hX hY f hf
    have : X.KanComplex := hX
    have : Y.KanComplex := hY
    exact DaggerActualQSingularFibrantWeakEquivalences.singular_GW f hf
  · intro K X hX hK
    have : X.KanComplex := hX
    exact DaggerActualKanCotensorParameterWeakEquivalences.constantHom_GW K X hK
  · intro X hX n
    have : X.KanComplex := hX
    exact DaggerActualQKanCotensorComparison.constants_row_GW X
      (Opposite.op (SimplexCategory.mk n))
  · intro X hX n
    have : X.KanComplex := hX
    exact DaggerActualKanSimplexCotensorComparison.singular_simplex_constants_GW X n

end DaggerActualQKanCotensorWeaknessChallenge
