# Accepted local Linux A/B/C/D verification

The current 2771-module source snapshot passed the local ARM64 Linux verification
and independent host acceptance on 2026-10-18. The separately executed restored
owner audit also passed independent aggregate acceptance. This is unpublished
local evidence; no hosted GitHub job or release is claimed.

The mathematical source revision is
`dfee9b568d8f67980b164fa830d189d106951a57`, with source graph SHA-256
`0a3af50bbf1dbb6ae6ddd5b679cb6d0120306c3f3d34777bc358cfd84859943f`.
Later documentation and packaging changes must retain all 2771 exact Lean
source paths, sizes and hashes in `SOURCE_MANIFEST.json` to use this evidence.

## Completed gates

- All 2771 modules passed the sequential build; ordinary `lake build` passed
  with 5717 jobs.
- The trusted data-only audit checked 40,022 owned declarations, 71 advertised
  results and eight main roots. Its only axioms were `propext`,
  `Classical.choice` and `Quot.sound`.
- Nine retained B/C/D comparisons passed with their prescribed outcomes,
  including fresh exports of public B, generic C and D. Positive cases passed
  the default Lean kernel. The saved C-universe-zero control was also retained.
- Five A comparisons passed with their prescribed outcomes: normal and frozen
  Challenge positives replayed in the default kernel; weakened `True`, extra
  axiom and changed `leftProper` candidates were rejected. Six external
  fixtures compiled and five environments were exported.
- All four compiled audit negatives were rejected: proof hole, unused public
  axiom, transitive external axiom and initializer spoof.
- After restoration, the complete owner audit was executed again. Its output
  was byte-identical to the initial positive. Before/after snapshots confirmed
  all 2771 source/olean pairs were unchanged.
- Strict Landrun and unprivileged user systemd were used, with the candidate
  write-denial control retained. No best-effort sandbox fallback was used.

The 71-result current metadata also passed against the actual Linux owner log.
The [portable summary](.ci/a/local-verification-summary.json) preserves the
native evidence and records this separate Linux scope. Its `Linux_CI_passed`
field refers to this accepted local aggregate, not hosted GitHub CI.

## Exact evidence binding

| Evidence | SHA-256 |
| --- | --- |
| Original successful main result | `35163ba5950b0ab590030d43f71391af74468940a98f696831266f65c0baf89f` |
| Independent resumed-main acceptance | `d926af64654d22e741d5b77957b1061c271f6cf197981889de40cc5972b73c6b` |
| Restored-owner supplement result | `dafc303f7a94ce432f638b8ccd113ea49a664363b703a706af4a65072389c12d` |
| Independent aggregate acceptance | `e1dc6ecd24838abc317ee635c87acd7f595437cffd763b561b00ed949511b73f` |
| Initial and restored owner logs | `0c3318eaf51dd4101127fe07ff1cbedf97c548afeaf070e09ec30d131b4568e5` |
| Before and after source/olean snapshot | `220e9ebd12692136a0989716dba96f2697a15fbfbcf0d7fdc7309bf9a4afc5b6` |
| Candidate source-module hash map | `07849ab1b2f7841bf386defe00a70317cddedd9c1983c608f5b09cdcafe0ecef` |

The main controller source was fixed at
`6a587aede3740e79af8f6b7f469d2769e269703ac7d85e3ebfeeceb16046ebfa`.
The separately executed restored-audit helper was fixed at
`6851b18ba17af7e9de4a529bd141a5cd43c46d1b76e4dd386c40a35421c13948`.
The aggregate reran the original host acceptance, checked the supplement's
binding to the successful main result, validated full owner coverage, and
compared both logs and snapshots byte for byte. The original raw result was
not rewritten to insert the later restored-audit result.

## Execution and publication boundaries

Earlier attempts stopped with memory or storage failures. This successful run
continued the retained partial cache after checking all 2771 source hashes and
2733 existing olean hashes. It is **not a cold independent rebuild**. It used
one CPU, 6 GiB guest RAM and initially 2 GiB swap; another 2 GiB swap was added
during the same source build. Dependency cache bind mounts and OverlayFS were
not used. The dedicated VM was shut down normally after evidence preservation.

The full updated controller was not executed as one integrated run. The accepted
local evidence is the preserved main run plus the independently bound restored
audit supplement. The proposed hosted workflow remains inactive and must run
on the final published commit before claiming hosted success.

A's 48-line Challenge imports a 366-module, 679,416-line project closure.
The B/C/D Challenges also import project definitions. These are recorded
exceptions to the Mathlib-only foundation Challenge convention. Agent manuscript
correspondence review is not independent human review; machine checks do not
establish the translation of prose into those specifications.

Both trusted-asset public URLs remain unset. Distribution terms for 180 copied
upstream files remain unconfirmed in [THIRD_PARTY_NOTICES.md](THIRD_PARTY_NOTICES.md).
The ordered public transaction and permanent paper evidence are described in
[PUBLISHING.md](PUBLISHING.md). No push, upload, new release or author contact
was performed by this local verification.
