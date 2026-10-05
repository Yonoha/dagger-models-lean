# Temporary Linux verification capability branch

This branch tests Linux verification restrictions using fresh probe-owned
fixtures. It does not build Part I, run Comparator, or distribute external
model-category source. The first two runs measured kernel/system-manager
prerequisites only. The current workflow additionally runs the production
Sandbox builder on harmless Python and Lean-standard-library fixtures.

The payload runs as the original non-root runner user. It must be unable to
write or chmod a read-only fixture, and unable to create UNIX or INET sockets,
while it can write a dedicated temporary output directory. Only those temporary
fixtures can be modified even if a restriction fails. The controller checks the
unchanged fixture and actual permitted output, and prints the precise errors.

The minimum ABI6 check is an environment prerequisite for the planned Landrun
signal/abstract-socket scoping. The probe does not install a Landlock ruleset.
Kernel capability queries follow the [Linux Landlock documentation](https://docs.kernel.org/userspace-api/landlock.html)
and the [pinned Linux UAPI syscall numbers](https://github.com/torvalds/linux/blob/v6.12/include/uapi/asm-generic/unistd.h).

The workflow uses the existing manual-dispatch path only on this isolated
branch. Its results must not be reported as the normal Lean verification job
or verification of any mathematical theorem. The main companion and its normal
verification workflow are unchanged. Commits skip unrelated automatic
proof/Comparator jobs; each probe is dispatched explicitly at its exact commit.

The initial run at commit `009c5c2e4a8c79c8bf5b3b0260ec973a52f1cbdd`
failed both filesystem denial checks on both runners, while socket denials and
the ABI6 prerequisite passed. That failed result is retained as
[run 37290623484](https://github.com/Yonoha/dagger-models-lean/actions/runs/37290623484).
Run [37291004332](https://github.com/Yonoha/dagger-models-lean/actions/runs/37291004332)
at `c4b741093e05e3b4486bc541bbfa6a62c9cda3f5` explicitly added the fixture root
to `ReadOnlyPaths` and passed both runners. Its mount entries retain the writable
home mount, explicitly read-only fixture parent and writable child output.

The production-builder phase uses byte-identical `verification_sandbox.py`
and `verification_denial_controls.py` from the separately frozen repair batch;
their expected SHA-256 values are enforced before execution. It builds the
unchanged pinned Landrun runner and installs Lean 4.27.0 without Mathlib cache
or a project build. Required effects include file/metadata/socket/signal/debug
denials, a permitted output write, and actual Lean elaboration plus serialized
artifact-import denial markers. The debug target is a disposable helper that
holds one literal byte; file probes do not write bytes even if denial fails.
Native results and complete command histories are printed even on failure.

Passing these standalone controls does not establish that the full package,
406-owner audit, metadata transaction, or Comparator passes. Production
adoption still requires independent review and those full integration gates.
