import ChallengeActualQSingularWeakReflection
import ActualQKanNaturalComparisons
import ProofActualQKanCotensorWeakness

set_option autoImplicit false
universe u
namespace DaggerActualQSingularWeakReflectionChallenge

theorem verified : statement.{u} := by
  constructor
  · intro X Y hX hY f
    have : X.KanComplex := hX
    have : Y.KanComplex := hY
    exact DaggerActualQKanNaturalComparisons.singular_GW_iff f
  · intro X hX
    have : X.KanComplex := hX
    exact ⟨DaggerBisimplicialDiagonal.diag (DaggerActualQKanCotensorComparison.mixed X),
      DaggerBisimplicialDiagonal.diagMap (DaggerActualQKanCotensorComparison.constants X),
      DaggerActualQSingularCotensorExchangeIso.singularComparison X,
      DaggerActualQKanCotensorComparison.diagonal_constants_GW X,
      DaggerActualQSingularCotensorExchangeIso.singularComparison_GW X⟩

end DaggerActualQSingularWeakReflectionChallenge
