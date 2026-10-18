# Theorem A: current verification scope

The local development now contains a universe-polymorphic bridge for manuscript
Theorem A (`bg.thm.main` and `bg.thm.left-proper`).
[ChallengeTheoremA.lean](ChallengeTheoremA.lean) specifies one model structure on
the original dagger simplicial categories, its weak equivalences, cofibrations
and fibrations, local finite presentability and small generating families with
finitely presentable domains, the trivial-fibration characterization, and left
properness for every pushout along an original cofibration.
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
and are unchanged. After earlier guest boot, memory and storage failures, the
resumed local ARM64 Linux run completed the 2771-module sequential build and
ordinary Lake build. Its all-owner audit covered 40,022 declarations, 71
advertised results and eight main roots with only the three standard axioms;
current metadata passed against that audit. All nine B/C/D lane cases,
including public re-exports from the current 2771-source snapshot, and five A
comparisons passed, including
default-kernel replay on positive cases. Four audit negative controls were
rejected. The A extension compiled six external fixtures and exported five
environments.

The original controller's main run and a separately executed restored-owner
audit supplement were independently accepted together for the same guest
project. The initial and restored audit logs are byte-identical with SHA-256
`0c3318eaf51dd4101127fe07ff1cbedf97c548afeaf070e09ec30d131b4568e5`;
the source/`.olean` snapshot before and after is
`220e9ebd12692136a0989716dba96f2697a15fbfbcf0d7fdc7309bf9a4afc5b6`.
The raw source result SHA-256 is
`35163ba5950b0ab590030d43f71391af74468940a98f696831266f65c0baf89f`;
the accepted aggregate SHA-256 is
`e1dc6ecd24838abc317ee635c87acd7f595437cffd763b561b00ed949511b73f`.
This is a partial-cache continuation, not a cold independent rebuild or a
single execution of the newer full controller. Hosted GitHub CI has not run.
The exact local evidence binding is in
[LINUX_VERIFICATION.md](LINUX_VERIFICATION.md).
The additive A asset passed local package/fetch readback, but its published URL
remains unset. No new GitHub publication or release is claimed.
