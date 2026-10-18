# Source integration and recovery

This working tree combines the previously published foundations with the saved
formal proofs of the frozen Lean statements for Main Theorems B, C and D.
`SOURCE_MANIFEST.json` records the exact local mathematical source inputs.
A manifest, a complete import graph, and a saved proof certificate are separate
from a successful build of this entire source tree. The integrated source build
is currently in progress. Public Linux CI has not yet checked this revision.

The previously published mathematical source files are preserved byte for byte.
The existing `DaggerModels` library target and its full published import barrel
are retained. Additional modules are explicitly registered in Lake; CI Challenge
files with specification placeholders are not library build inputs. Modules
whose bare names alias canonical `DaggerModels.*` modules contain only imports,
so their declarations are defined once. Pinned upstream Mathlib files are reused
from the dependency rather than copied into this package.

Some historical source files were recovered literally from saved development
records, with recorded SHA256 checks. Where the original handwritten proof
script was unavailable, the source contains the preserved closed declaration
terms, sometimes as a literal expression DAG decoded by
`OriginalRecoveredClosedExpression.lean`. These are proof terms checked by the
ordinary Lean elaborator and kernel. The decoder accepts only closed syntax
and forbids metavariables; it does not load mathematical declarations from a
previous `.olean` file. Its implementation is part of this source tree.

In particular, `AmalgamEvaluation.lean` was reconstructed from the saved types
and values of fourteen declarations. It was recompiled, and all fourteen
constant records matched the originals using Lean expression equality, which
ignores bound-variable names. Its original handwritten script is unavailable.
This fidelity check is distinct from the full source build and from manuscript
correspondence. Generated raw proof terms are less convenient to read than a
handwritten tactic proof; that limitation is explicit.

The B/C/D specification modules import prior project definitions. They are not
self-contained Mathlib-only Challenges. Comparator must compare fresh candidate
proofs to independently frozen specification exports, including the referenced
definition closure. Rebuilding both the specification and its dependencies from
the candidate would not protect against changing their meaning together.
The frozen portable certificate replay has passed locally, including theorem
mismatch and forbidden-axiom controls. It does not by itself validate a modified
candidate source tree or establish correspondence with the manuscript.

The existing 27 Mathlib-only Comparator groups and their weakened-statement and
changed-definition controls are retained. Their dependency pins and Challenge
validator are unchanged. New source-build, axiom-audit, B/C/D frozen-specification
comparisons and actual Linux CI must be recorded separately before the integrated
revision is described as fully verified. No independent human review of the
Lean-to-manuscript correspondence is claimed.
