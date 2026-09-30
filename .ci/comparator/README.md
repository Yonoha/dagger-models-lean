# Statement and definition preservation with Comparator

The [Comparator workflow](../../.github/workflows/comparator.yml) uses
[leanprover/comparator](https://github.com/leanprover/comparator) to compare the
candidate against **commit `dce8401a23588ba65b8aa4ca41de26cb0203d444`**, the original
v0.1.0 source. The reference is fetched independently at that full commit hash;
it is never reconstructed from the candidate's current definitions.

The checker covers the **21 named library theorems** in `config.json` and their
statement dependencies. Three additional reflexive statements in
`Contracts.lean` make `FreeCofibration`, `nonDegenerateEquiv`, and `forget` roots
of the recursive definition comparison. These statements are audit markers,
not new mathematical results, and are not imported by `DaggerModels.lean`.
No definition holes are enabled.

The reference module contains the original definitions and proofs, without
introducing `sorry`. The candidate module imports the proposed `DaggerModels`
sources. Comparator checks statement equality, the relevant transitive
definitions, permitted axioms, and replays the exported proof dependencies in
its Lean kernel. Changing a theorem's type to `True`, or changing
`FreeCofibration` to the vacuous condition `f = f`, is required to fail with a
specific comparison diagnostic. A compilation error alone is not accepted as
evidence that either negative control worked.

## Trust boundary

This checks preservation of the chosen Lean baseline. It does **not** establish
that this baseline faithfully translates the informal manuscript. The reference
was produced with AI assistance and is recorded as agent-reviewed, not
independently human-reviewed, in `formalization.yaml`.

On pull requests, `pull_request_target` executes the **base branch's** control
files. The candidate checkout is treated as data: only its Lean library sources
are copied into an isolated project. Its Lake configuration, dependency pins,
shell/Python scripts, workflows, and prebuilt artifacts are not executed or
reused. All checkouts disable credential persistence and the workflow has only
read permission. Separate writable artifact directories are used for each case.

Comparator builds and exports the candidate with the actual Linux Landrun
sandbox. The upstream-recommended systemd restriction on AF_UNIX sockets is
also applied, and comparison runs as the unprivileged runner user. There is no
fake-landrun fallback. Candidate artifacts are never subsequently loaded outside
the sandbox. The ordinary build/axiom/metadata job runs on a separate runner.

The baseline hash, comparison target list, contracts, trusted preparer, tool
pins, and workflow are trusted inputs. Changes to these files need explicit
review: a maintainer who changes both the target and its checker can still
change what is being checked. Repository administration and branch protection
are not established by this workflow. Newly added mathematical results must be
registered explicitly; the current target list is not a claim of coverage for
future declarations.

## Pinned tools

| Component | Revision |
| --- | --- |
| Comparator | `fd5d5bcf14177b187f66d4502071268d877887c3` |
| Exporter for Lean 4.27.0 | `590dec59d93ab6becdf16fdd8aee5abbb99cb856` |
| Landrun | `811cfff51ceaf3d9843708aa6d22e9b84ccac8b4` |

Comparator is built with the toolchain in its own pinned repository. The
exporter and both proof projects use the companion's original Lean 4.27.0
toolchain. See the workflow for executable setup and the two deliberate
negative controls. This Linux check is separate from the macOS-compatible
`lake build`, axiom audit, and metadata validation commands.

## Updating the mathematical baseline

First review the proposed statements, definitions, hypotheses, and manuscript
correspondence. Then record a new immutable reference revision, update the
comparison targets and `formalization.yaml`, and rerun both positive and
negative checks. Do not automatically replace the reference with the candidate
when Comparator reports a mismatch. Dependency or Lean upgrades may also require
an explicit reference migration, because Comparator checks the elaborated
statements and their definitions, not merely displayed source text.
