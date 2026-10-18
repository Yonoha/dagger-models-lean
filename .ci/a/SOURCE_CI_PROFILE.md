# Current source CI profile: local Linux verification accepted

`scripts/bcd_source_ci.py --source-profile current-2771` adds a release-snapshot
verification profile for the current 2771-module source graph. The default
`retained-2767` profile keeps the historical B/C/D lane. The new profile does not
activate itself in the staged public workflow.

The current profile requires these independently fixed inputs:

| Input | SHA-256 |
| --- | --- |
| Full 2771-module source graph | `0a3af50bbf1dbb6ae6ddd5b679cb6d0120306c3f3d34777bc358cfd84859943f` |
| Expanded data-only auditor source | `c513a930965ed19cc6d757276b6d83675eb44992bc87c1bcaefcd8ae3365db03` |
| 2771 owners | `149da9a29e3cd8535e14acdb9e0c487c7692d4191fd5e9db97c03e1bee273aa2` |
| 71 advertised results | `1c8b6763d2dfef7e29d8c2142f7a07d919a7340ef9e77efa33c98c97ec0806eb` |
| 8 main roots | `972cb0bee03545626e32f817aefb8a84603982f2a8e507c9ae57da01d9219b5b` |

It checks every source file's path, size and hash before and after staging;
generates its own Lake configuration; builds all 2771 modules; and uses the
expanded owner auditor. It retains the B/C/D exports, existing Comparator cases,
strict Landrun requirements, and four audit negative controls. For this profile
the audit mutation controls use the final `MainTheoremsABCD` aggregate so their
test overlays do not invalidate compiled downstream imports.

This profile deliberately fixes a release snapshot, including proof source
bytes. It is not a general gate for accepting changed proof implementations.
Updating that snapshot requires an explicit review of the trusted graph and
inputs. A-specific frozen Comparator verification is available through the
paired optional `--a-extension` and `--a-extension-manifest-sha256` arguments.
The latter must come from an independently reviewed trusted lock. The helper
checks the exact expanded asset, compiles six external fixtures, exports five
environments and runs five A comparisons after the existing B/C/D gates.
Compiler writes are restricted to each fresh olean output directory; fixed
Challenge bytes are rechecked before every frozen comparison and on exit.
Only complete success permits A and ABCD aggregate flags to become true.
Without this extension both flags remain explicitly false. The default
retained profile does not load the A helper.

The real additive A asset passed full local fetch verification and the extension
preflight. Matching 71-result metadata passed the current-scope checker against
the actual expanded audit. The resumed local ARM64 Linux partial-cache
continuation passed the 2771-module sequential and ordinary Lake builds, the
40,022-declaration/71-result/eight-main-root audit, all nine B/C/D lane cases
(including current public re-exports), five A cases, and four rejected audit
mutations. The A extension compiled six
external fixtures and exported five environments. A separate supplement on
the same guest project repeated the all-owner audit byte for byte with every
source and `.olean` file unchanged; the combined local result was accepted.
The original raw result SHA-256 is
`35163ba5950b0ab590030d43f71391af74468940a98f696831266f65c0baf89f`;
the accepted aggregate SHA-256 is
`e1dc6ecd24838abc317ee635c87acd7f595437cffd763b561b00ed949511b73f`.
This is neither a cold rebuild nor one execution of the newer integrated
controller. See [ASSETS.md](ASSETS.md) for the pinned local hashes and pending
public URL. Fetch receipts must be retained outside the exact trusted payload
before passing that payload to the runner.

Eight Python staging/validation fixtures and nine A-helper fixtures passed
locally. A separate agent reviewed the A helper's boundaries and the compiler
write scope was narrowed following that review. These checks do not execute
Lean, the auditor, the exporter, Comparator, or Linux. Those fixtures are
separate from the actual local Linux execution described above. No hosted
GitHub CI success or release is claimed.

The prepared hosted wrapper, its input boundaries and the exact-70 to exact-71
workflow transition are described in [HOSTED_CI.md](HOSTED_CI.md). Its workflow
preparation file is not active and still requires actual runtime verification.
