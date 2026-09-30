# Lean formalization workflow

The manuscript is the mathematical source of truth. Do not silently change a
definition, theorem statement, hypothesis, universe, or scope to obtain a proof.
Explain any proposed mathematical change before making it. A successful Lean
build does not establish correspondence with the manuscript.

## Models and delegation

- For implementation from an existing detailed mathematical proof, use a
  `gpt-6.1-sol` subagent with `xhigh` reasoning by default. This project authorizes
  that delegation when it is useful; small routine edits need no extra agent.
- Use a separate `gpt-6.1-sol` / `xhigh` reviewer for substantive changes to
  Challenge statements or their manuscript correspondence. Give the reviewer
  the source definitions and precise manuscript labels, not just a build log.
- Keep assignments bounded and owned files disjoint. Avoid redundant agents.
- Escalate a difficult implementation to `ultra` only after identifying the
  concrete obstacle. Explain the reason rather than silently increasing effort.
- Distinguish a Lean implementation obstacle from a missing mathematical proof.
  Astra may be appropriate for the latter; it is not the default for translating
  an existing proof. These instructions do not change the main chat's model.

## Lean skill

Use the `lean4` skill from
[cameronfreer/lean4-skills](https://github.com/cameronfreer/lean4-skills).
Read its `SKILL.md` when beginning Lean work; search existing mathlib results,
preserve declaration signatures, and validate incrementally.
The initial installation used revision
`b6243b85b9b0a0ddff5bb6773889044daf687f8e`, core skill and references only.
Do not claim that helper scripts, hooks, or Lean LSP tools are installed merely
because the core skill is installed. Use available Lean/Lake tooling and this
repository's audits when those optional capabilities are unavailable.

## Challenge and verification

- A Challenge contains the problem's definitions and statement skeletons.
  It must import only pinned `Mathlib` modules, never candidate modules or a
  local file that conceals the implementation or its proofs.
- Aim for at most 100 physical lines per self-contained Challenge, including
  imports, comments, and blank lines. Report the total across all Challenges.
  Do not achieve a short count by hiding context in local imports or by golfing
  unreadable lines. Discuss any necessary exception; never exceed 500 lines.
- Challenge proof placeholders are specification markers, not proved results.
  Keep them outside the library. Do not allow definition holes in Comparator.
- Retain all registered comparison targets when reorganizing the checker.
  Changing trusted Challenges, targets, or dependency pins requires an explicit
  explanation of the mathematical and verification consequences.
- Check `lake build`, the transitive axiom audit, the audit's negative controls,
  and metadata consistency. Run the real Linux Comparator job, including its
  weakened-statement and changed-definition negative controls.
- Keep `formalization.yaml` and `CORRESPONDENCE.md` honest about partial results,
  AI assistance, and review status. Agent review is not independent human review.

Do not edit the separately maintained LaTeX manuscript unless the task requires
it. Follow its own editing and compilation instructions when it does.
