# Native Comparator probe for free simplicial paths

This is a bounded experiment for the law-marker specification of free simplicial
paths. It compares the exact 24 registered theorem targets in `payload/config.json`
with the pinned native Lean Comparator on an Ubuntu runner. It is separate from
the repository's existing Comparator groups and formalization registry.

The standalone Challenge has 463 physical lines and imports only pinned Mathlib
modules. The candidate has 492 lines. The Challenge's proof holes are specification
markers; the candidate supplies the proofs and is built with warnings treated as
errors. Both use Lean 4.27.0 and the exact existing Mathlib manifest. Comparator
and its external exporter retain their existing, separately pinned toolchains.

`definition_names` is empty because these 24 entry points are theorem targets.
This does not mean that definitions are absent or ignored: the native comparison
also follows the definitions and proof dependencies required by those targets.
The run must actually succeed before any native-comparison claim is made.

The workflow runs three isolated cases:

- A weakened-statement control changes only the candidate's `enrichment_eq`
  conclusion to `True`, keeping the universally quantified graph argument. Its
  unused binder is named `_G`. Native theorem-statement comparison must reject it.
- A changed-definition control replaces the candidate enrichment's Hom expression
  with a separately named copy of the same expression. Native definition
  comparison must reject this change even though Lean can unfold the copy.
- The exact positive candidate must pass native comparison for all 24 targets.

A control succeeds only after the Challenge and Solution build/export phases and
an actual Comparator exit code of 1 with the expected named mismatch. A setup,
Lean build, export, timeout, or unrelated failure does not count as a successful
negative control. The positive case requires exit code 0 and Comparator's success
message. The launcher uses the existing Landrun/systemd isolation route.

The `Law marker probe24` workflow retains the exact input sources, configuration,
launcher arguments, separate raw stdout/stderr, outcomes, and available own build
artifacts for 30 days. Its combined log concatenates stdout and stderr and does
not claim chronological interleaving. A timeout is recorded as unknown/live and
stops subsequent cases; it is never an accepted comparison.

Passing this probe is evidence for this exact pair and its 24 targets. It does
not certify the complete Part I manuscript, the entire model-category theorem,
or an independent identification of every abstract carrier in a compact global
Challenge. It is AI-assisted work and has not received independent human review.
