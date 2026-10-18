# Current A/B/C/D hosted CI preparation

The helper scripts are installed, and `hosted-comparator.yml.proposed` is a
reviewable workflow preparation file. It is outside `.github/workflows` and
does not activate a job. No successful hosted VM or current-source Linux run
has been recorded for this preparation.

The host checks both control and candidate checkout revisions before using
them, fetches B/C/D and additive A assets from independent trusted locks, and
stages exactly the SHA-pinned 2771 Lean sources. It builds the pinned tools and
an isolated trusted auditor. Candidate build configuration is not executed on
the host. A fresh hosted x64 runner with KVM is required; SDK cleanup is guarded
to that environment.

The guest uses a fixed Debian cloud image and a fixed snapshot index for kernel
7.2.6. It must demonstrate Landlock ABI 9 or later and run as an unprivileged
user. Strict Landrun and user systemd remain required. The current source runner
builds all 2771 modules, audits the 71 advertised results and eight main roots,
retains the nine B/C/D Comparator cases and four audit negatives, and adds the
five A comparisons. The host checks the copied result and audit-log hash, then
independently validates exact current metadata before writing its receipt.

The A fetcher writes a fetch receipt next to the verified payload. The host
validates that receipt and moves it outside the payload before mounting the
exact A input tree read-only. The A manifest hash is taken from the trusted
control lock, rather than calculated from candidate-provided inputs.

The guest prepares the unchanged trusted cache project, then uses
`current_mathlib_cache.py` to select every Mathlib import in the pinned full
source graph. The current graph has 316 distinct direct Mathlib imports; the
official cache tool follows all their transitive imports. Lean and Std modules
come from the toolchain. This changes which prebuilt dependency caches are
downloaded, while the source runner still builds all 2771 local modules and
retains every proof, audit and comparison target. The helper verifies the graph,
both dependency pin files and the exact generated Lakefile before invoking Lake.
`--plan-only` prints the complete selection without running Lake. Actual disk
savings and cache download success have not yet been measured in the guest.

## Activation conditions

The actual current native source build, expanded audit and A Comparator must
first pass. Generate and review the real additive A asset, register the actual
A metadata/configuration, verify the current Linux route, and populate reviewed
asset locks. Both public archive URLs remain unconfigured until publication.
Null or missing pins fail before tool or image setup.

Once those conditions are met, use this workflow to replace the staged
`.github/workflows/bcd-comparator.yml`. All nine old comparison cases and four
audit negatives remain required in the replacement. Keep the foundation
workflows and all registered foundation targets. The retained source-runner
profile also remains available for historical snapshots.

Do not run the old exact-70 metadata job against a newly registered 71-result
manifest and interpret its rejection as a proof failure. The replacement uses
`check_metadata.py --scope current`, which checks all 71 results. The historical
`--scope full` deliberately keeps its exact-70 contract.

Static checks cover source staging, all 34 guest CLI options, workflow/script
syntax, the pinned snapshot index, and a synthetic complete result plus 26
missing/changed-result rejection cases. A separate agent reviewed the result
gate. These checks do not establish actual VM boot, Lean compilation, Landrun
enforcement, Comparator success or Linux acceptance.
