# Temporary Linux verification capability branch

This branch measures the hosted runner's Landlock ABI and system-manager
filesystem/syscall restrictions using fresh probe-owned fixtures. It invokes
no candidate Lean code, external model-category source, Lake build, proof audit
or Comparator. It does not validate the production isolation implementation.

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
branch. Its results must not be reported as the normal Lean verification job,
verification of any mathematical theorem, or native production-sandbox
acceptance. The main companion and its normal verification workflow are
unchanged. The commit skips unrelated automatic proof/Comparator jobs; the
capability workflow is dispatched explicitly and its exact commit is recorded.
