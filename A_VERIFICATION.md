# Theorem A: current verification scope

The local development now contains a universe-polymorphic bridge for manuscript
Theorem A (`bg.thm.main` and `bg.thm.left-proper`).
[ChallengeTheoremA.lean](ChallengeTheoremA.lean) specifies one model structure on
the original dagger simplicial categories, its weak equivalences, cofibrations
and fibrations, finite generating data, the trivial-fibration characterization,
and left properness for every pushout along an original cofibration.
[ProofTheoremA.lean](ProofTheoremA.lean) applies the existing model construction
and left-properness proofs; it does not infer A from Theorems B, C or D.
[MainTheoremsA.lean](MainTheoremsA.lean) exposes
`DaggerComparator.mainA : DaggerTheoremAChallenge.statement.{u}`.
[MainTheoremsABCD.lean](MainTheoremsABCD.lean) imports the A and B/C/D public names.

The three A modules passed serial Lean 4.27.0 compilation locally, using the
previously accepted dependency `.olean` files. The final sources contain no
`sorry` or `admit`; `#print axioms DaggerComparator.mainA` reported only
`propext`, `Classical.choice` and `Quot.sound`. The explicit weak-equivalence
predicate agrees definitionally with `daggerDK standardReplacement`. The proof
retains the original generating classes, the geometric trivial Kan condition,
the standard fixed-object fibrant replacement, and the arbitrary universe `u`.

A separate agent compared the statement and proof with the manuscript and found
no concrete weakening or import cycle. This is agent review. Independent human
review has not been recorded. The 48-line Challenge imports project definitions;
it is not a self-contained Mathlib-only specification, and its line count does
not bound the amount of context that needs review. Its project import closure
contains 366 local modules and 679,416 source lines.

The [portable local summary](.ci/a/local-verification-summary.json) records
the separate local verification gates. The current 2771-module source
closure includes the A bridge and the two comment-only third-party modification
notices. Its sequential and ordinary Lake builds passed locally; the accepted
build receipt SHA-256 is recorded in the portable summary.
The expanded data-only audit passed for all 2771 modules and 40,022 owned
declarations, including 71 advertised results, eight main roots, four rejected
negative controls and a byte-identical restored positive. The 71-result
`formalization.yaml` metadata passed `check_metadata.py --scope current`.
The local A-specific Comparator run passed five A cases plus five retained
portable controls: the A normal and public positive cases replayed, while the
weakened statement, extra axiom and changed `leftProper` definition were
rejected. The trusted A statement was unchanged by those negative fixtures.
The retained B/C/D certificates and their 70-result metadata do not certify A
and are unchanged; re-export comparison of B/C/D from the new 2771-source
snapshot remains for Linux verification. The attempted Linux VM did not reach
the checks because its guest entered emergency mode with `nls_ascii` missing;
Linux CI has not passed. The additive A asset passed local package/fetch
readback, but its published URL remains unset. No new GitHub publication or
release is claimed.
