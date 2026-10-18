#!/usr/bin/env python3
"""Fail-closed staged B/C/D Linux source Comparator runner; not yet executed.

The caller must supply independently pinned/trusted inputs. Never run this from
the candidate checkout, and never take --graph, --frozen or --pins from it.
The additive current-2771 profile also builds A source and audits its roots.
With an independently pinned A extension, it adds the A Comparator cases;
without that extension, its Comparator result covers B/C/D only.
"""

import argparse
import gzip
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import stat
import subprocess
import sys

from lean_imports import header_imports


PACKAGE_MANIFEST_SHA256 = "42e1ed4e30b7988d797bf8afa040d4b77fe459f8f113539ab5d245ea6bebe690"
EXPORT_INDEX_SHA256 = "350faac7fd9886f5beb4fdc35b2b2992bbd214aac0571199f1d8080ce705a13d"
CASE_INDEX_SHA256 = "45d89e063f9d4ba409d860f1bb275bdf57fdc21e9212f97142d88b4af6b6d997"
FIXTURE_MANIFEST_SHA256 = "12e013e53765775bd38d2f6be6cd22c66700ed485e9d5017a86dd76450077756"
FIXTURE_CASE_SHA256 = "747cec03e2a4f2465e436fe8e03005cd35a8b271e3158c4ea4861844cd41c9f4"
PINS_MANIFEST_SHA256 = "1c6eb229691c7b0d1b38a574a7897e19dbe7f0bc2674d62c640fdc2e105e3c48"
PINS_TOOLCHAIN_SHA256 = "d55ca0039a5479db5b38919d005b2c427b89b3be4f0184a20f2f4eae931f5bdb"
GENERIC_C_RAW_SHA256 = "004b6e63577547fb8e39cdc13d1ae22d5693ffef4365bd7ddbead359580759db"
GENERIC_C_RAW_BYTES = 174986221
GENERIC_C_GZIP_SHA256 = "96a0a5456a63930ef710131e25d13566898659742dea37d4098925e30001a55b"
GENERIC_C_GZIP_BYTES = 46003202
GENERIC_C_MANIFEST_SHA256 = "c247d0244d21a48e02359225b1428d8e168d4f99c4efb5fa9616b537f5d3aa67"
GENERIC_C_EXTENSION_SHA256 = "ccb4939cc13bdaa204e5971347ea739cbce6a8693d3522dcca96495edfc47520"
GENERIC_C_SOURCE_SHA256 = "8094f792618d0f58e456c094e88a258c8892e65c4cd9cdbcad46d32e1f0b47ab"
GENERIC_C_GUARD_SHA256 = "4adcf11bc0048701571672f3d80a098c63d8639941b7d7911d7a323d0cf54bb5"
GENERIC_C_GUARD_RESULT_SHA256 = "c388443ff4653954066669a331014efb83e90c96e3f2be2c4a0079deac9de3ef"
CHALLENGE_SHA256 = {
    "B": "5bb5ab20a101414222f0c0b3c7f569ef62d21d4105408397d56e4e35f55afb9c",
    "C": "0a51c04a5ce1919234a1c338398937484e1092475847153fb2e520ec3e60f488",
    "D": "e19ffded19a04e5ee645f8c3804b0e341158f01b124080374893464c20e781b5",
}
PUBLIC_MODULE = "MainTheoremsBCD"
ROOTS = {
    "B": "DaggerComparator.mainB",
    "C": "DaggerComparator.originalMainTheoremC",
    "D": "DaggerComparator.mainD",
}
MAIN_RESULTS = (
    "DaggerActualMainTheoremBProof.verified",
    "DaggerProofOriginalMainTheoremC.verified",
    "ProofActualMainTheoremD.verified",
    *ROOTS.values(),
)
RETAINED_PROFILE = "retained-2767"
CURRENT_PROFILE = "current-2771"
CURRENT_GRAPH_SHA256 = "0a3af50bbf1dbb6ae6ddd5b679cb6d0120306c3f3d34777bc358cfd84859943f"
CURRENT_AUDITOR_SOURCE_SHA256 = "c513a930965ed19cc6d757276b6d83675eb44992bc87c1bcaefcd8ae3365db03"
CURRENT_OWNERS_SHA256 = "149da9a29e3cd8535e14acdb9e0c487c7692d4191fd5e9db97c03e1bee273aa2"
CURRENT_ADVERTISED_SHA256 = "1c8b6763d2dfef7e29d8c2142f7a07d919a7340ef9e77efa33c98c97ec0806eb"
CURRENT_MAIN_SHA256 = "972cb0bee03545626e32f817aefb8a84603982f2a8e507c9ae57da01d9219b5b"
CURRENT_GRAPH_ROOTS = ("DaggerModels", "MainTheoremsABCD")
CURRENT_MAIN_RESULTS = MAIN_RESULTS + (
    "DaggerTheoremAProof.verified", "DaggerComparator.mainA",
)
CURRENT_CHANGED_SOURCE_SHA256 = {
    "TopCatModelCategory.SSet.Simplices":
        "cd31bb18a767601751559e8902bb7706903ebc5841354f7be90336dd01ea2174",
    "TopCatModelCategory.SSet.Subcomplex":
        "433bde33467204d4707c5731e5197050e552882854689a65b517ee152f9acebd",
}
AXIOMS = ("propext", "Quot.sound", "Classical.choice")
PRIMITIVES = (
    "Nat.add", "Nat.sub", "Nat.mul", "Nat.pow", "Nat.gcd", "Nat.div",
    "Nat.mod", "Nat.beq", "Nat.ble", "Nat.land", "Nat.lor", "Nat.xor",
    "Nat.shiftLeft", "Nat.shiftRight", "String.ofList",
)
NAME = re.compile(r"[A-Za-z_][A-Za-z_0-9]*(?:\.[A-Za-z_][A-Za-z_0-9]*)*")


def profile_spec(name: str) -> dict:
    if name == RETAINED_PROFILE:
        return {"modules": 2767, "advertised": 70, "main": MAIN_RESULTS,
                "roots": ["DaggerModels", "ProofActualMainTheoremB",
                          "ProofOriginalMainTheoremC", "ProofActualMainTheoremD",
                          PUBLIC_MODULE], "last": PUBLIC_MODULE}
    if name == CURRENT_PROFILE:
        return {"modules": 2771, "advertised": 71, "main": CURRENT_MAIN_RESULTS,
                "roots": list(CURRENT_GRAPH_ROOTS), "last": "MainTheoremsABCD"}
    raise ValueError(f"unknown source profile: {name}")


def check_profile_pins(a: argparse.Namespace) -> None:
    if a.source_profile != CURRENT_PROFILE:
        return
    required = {
        "graph_sha256": CURRENT_GRAPH_SHA256,
        "auditor_source_sha256": CURRENT_AUDITOR_SOURCE_SHA256,
        "audit_owners_sha256": CURRENT_OWNERS_SHA256,
        "audit_advertised_sha256": CURRENT_ADVERTISED_SHA256,
        "audit_main_sha256": CURRENT_MAIN_SHA256,
    }
    for key, expected in required.items():
        if getattr(a, key) != expected:
            raise ValueError(f"current-2771 trusted input pin mismatch: {key}")


def a_extension_requested(a: argparse.Namespace) -> bool:
    if (a.a_extension is None) != (a.a_extension_manifest_sha256 is None):
        raise ValueError("--a-extension and --a-extension-manifest-sha256 must be supplied together")
    if a.a_extension is None:
        return False
    if a.source_profile != CURRENT_PROFILE:
        raise ValueError("A extension requires --source-profile current-2771")
    if not re.fullmatch(r"[0-9a-f]{64}", a.a_extension_manifest_sha256):
        raise ValueError("A extension manifest needs an independently pinned SHA256")
    return True


def digest(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            h.update(block)
    return h.hexdigest()


def checked(path: Path, expected: str) -> Path:
    if not path.is_file() or digest(path) != expected:
        raise ValueError(f"trusted input SHA256 mismatch: {path}")
    return path


def verify_package(root: Path, manifest_sha: str) -> None:
    manifest = json.loads(checked(root / "manifest.json", manifest_sha).read_text())
    if "files" in manifest and isinstance(manifest["files"], list):
        rows = manifest["files"]
    elif isinstance(manifest, dict):
        rows = [{"path": path, "sha256": value} for path, value in manifest.items()]
    else:
        raise ValueError("invalid trusted package manifest")
    if not rows:
        raise ValueError("empty trusted package manifest")
    seen = set()
    for row in rows:
        rel = Path(row["path"])
        if rel.is_absolute() or ".." in rel.parts or rel in seen:
            raise ValueError(f"unsafe or duplicate manifest path: {rel}")
        seen.add(rel)
        current = root
        for part in rel.parts:
            current = current / part
            if current.is_symlink():
                raise ValueError(f"symlink in trusted package: {current}")
        checked(current, row["sha256"])
        if "bytes" in row and current.stat().st_size != row["bytes"]:
            raise ValueError(f"trusted package size mismatch: {current}")


def ordinary_candidate_source(checkout: Path, relative: Path) -> Path:
    """Reject symlinks at every component; never follow candidate paths."""
    current = checkout
    if current.is_symlink() or not current.is_dir():
        raise ValueError(f"invalid candidate checkout: {checkout}")
    for part in relative.parts:
        current = current / part
        if current.is_symlink():
            raise ValueError(f"candidate symlink: {current}")
    if not stat.S_ISREG(current.stat(follow_symlinks=False).st_mode):
        raise ValueError(f"candidate source is not a regular file: {current}")
    return current


def inventory_names(path: Path, expected_sha: str) -> list[str]:
    lines = checked(path, expected_sha).read_text().splitlines()
    if not lines or len(lines) != len(set(lines)) or any(not NAME.fullmatch(n) for n in lines):
        raise ValueError(f"invalid trusted audit inventory: {path}")
    return lines


def checked_header_imports(path: Path, owner: str, allowed: set[str],
                           external: set[str]) -> None:
    for imported in header_imports(path):
        if imported not in allowed and imported not in external:
            raise ValueError(f"Import escapes pinned source closure: {owner}: {imported}")


def lakefile_for(modules: list[str]) -> str:
    # This is generated in trusted code, never copied from candidate lakefile.lean.
    globs = []
    for name in modules:
        if not NAME.fullmatch(name):
            raise ValueError(f"unsafe module name: {name}")
        globs.append(f"    .one `{name},")
    # Lake's roots are Name values. Dotted modules belong in exact module
    # globs; their first component is a root (as in the reviewed lakefile).
    root_names = sorted({name.split(".")[0] if "." in name else name
                         for name in modules})
    roots = [f"    `{name}," for name in root_names]
    return (
        "import Lake\nopen Lake DSL\n"
        "set_option maxRecDepth 20000\n"
        "package «dagger-models-lean» where\n"
        "  moreLeanArgs := #[\"-DwarningAsError=true\"]\n"
        "require mathlib from git\n"
        "  \"https://github.com/leanprover-community/mathlib4.git\" @\n"
        "    \"a3a10db0e9d66acbebf76c5e6a135066525ac900\"\n"
        "@[default_target]\n"
        "lean_lib DaggerModels where\n"
        "  roots := #[\n" + "\n".join(roots) + "\n  ]\n"
        "  globs := #[\n" + "\n".join(globs) + "\n  ]\n"
        "script buildSequential (args) do\n"
        "  let [orderFile] := args | throw <| IO.userError \"Expected a module-order file\"\n"
        "  let workspace ← getWorkspace\n"
        "  let contents ← IO.FS.readFile orderFile\n"
        "  let modules := contents.splitOn \"\\n\" |>.filter (· != \"\")\n"
        "  workspace.runFetchM do\n"
        "    for (name, index) in modules.zipIdx do\n"
        "      let some mod := workspace.findModule? name.toName\n"
        "        | error s!\"Unknown registered module: {name}\"\n"
        "      IO.println s!\"START_SOURCE {index + 1} {modules.length} {name}\"\n"
        "      let job ← mod.leanArts.fetch\n"
        "      let _ ← job.await\n"
        "      IO.println s!\"BUILT_SOURCE {index + 1} {modules.length} {name}\"\n"
        "      (← IO.getStdout).flush\n"
        "  return 0\n"
    )


def stage(a: argparse.Namespace) -> Path:
    if a.work.exists():
        raise ValueError("work directory must be fresh")
    spec = profile_spec(a.source_profile)
    check_profile_pins(a)
    if a.source_profile == CURRENT_PROFILE:
        checked(a.auditor_source, CURRENT_AUDITOR_SOURCE_SHA256)
    graph = json.loads(checked(a.graph, a.graph_sha256).read_text())
    if (graph["local_module_count"] != spec["modules"]
            or len(graph["local_source_modules"]) != spec["modules"]
            or graph["unresolved_nonstandard_imports"]):
        raise ValueError("frozen graph coverage changed")
    names = [row["module"] for row in graph["local_source_modules"]]
    if len(set(names)) != spec["modules"] or any(not NAME.fullmatch(n) for n in names):
        raise ValueError("invalid module allowlist")
    if names.count(PUBLIC_MODULE) != 1:
        raise ValueError("public aggregate module absent from frozen allowlist")
    if a.source_profile == CURRENT_PROFILE:
        if names.count("MainTheoremsABCD") != 1:
            raise ValueError("current public aggregate absent from source graph")
        by_name = {row["module"]: row for row in graph["local_source_modules"]}
        if any(by_name[name]["sha256"] != expected
               for name, expected in CURRENT_CHANGED_SOURCE_SHA256.items()):
            raise ValueError("current annotation source hashes differ")
    allowed = set(names)
    # Only external imports recorded by the SHA-pinned graph may be added to
    # candidate modules. This bounds the dependency set even within Mathlib.
    external = {imp for row in graph["local_source_modules"]
                for imp in row["imports"] if imp not in allowed}
    dependency_roots = {"Lean", "Init", "Std", "Mathlib", "Aesop", "Qq",
                        "Batteries", "ProofWidgets", "ImportGraph", "Plausible",
                        "LeanSearchClient"}
    if any(not NAME.fullmatch(imp) or imp.split(".", 1)[0] not in dependency_roots
           for imp in external):
        raise ValueError("accepted graph has an unknown external import")
    ordered = [n for n in graph["topological_order"] if n in allowed]
    if (len(ordered) != spec["modules"] or set(ordered) != allowed or
            ordered[-1] != spec["last"] or
            (a.source_profile == CURRENT_PROFILE and
             len(graph["topological_order"]) != spec["modules"])):
        raise ValueError("topological order does not cover the allowlist")
    if graph["roots"] != spec["roots"]:
        raise ValueError("unexpected frozen roots")
    manifest = json.loads(checked(a.pins / "lake-manifest.json", PINS_MANIFEST_SHA256).read_text())
    mathlib = [p for p in manifest["packages"] if p["name"] == "mathlib"]
    if len(mathlib) != 1 or mathlib[0]["rev"] != "a3a10db0e9d66acbebf76c5e6a135066525ac900":
        raise ValueError("Mathlib pin mismatch")
    if checked(a.pins / "lean-toolchain", PINS_TOOLCHAIN_SHA256).read_text().strip() != "leanprover/lean4:v4.27.0":
        raise ValueError("Lean pin mismatch")
    project = a.work / "candidate-project"
    project.mkdir(parents=True)
    source_hashes = {}
    for name in names:
        rel = Path(*name.split(".")).with_suffix(".lean")
        src = ordinary_candidate_source(a.candidate, rel)
        if a.source_profile == CURRENT_PROFILE:
            row = by_name[name]
            if row.get("path") != rel.as_posix() or src.stat().st_size != row.get("bytes"):
                raise ValueError(f"current source graph path/byte mismatch: {name}")
            checked(src, row["sha256"])
        checked_header_imports(src, name, allowed, external)
        dst = project / rel
        dst.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(src, dst)
        staged_sha = digest(dst)
        if a.source_profile == CURRENT_PROFILE and staged_sha != row["sha256"]:
            raise ValueError(f"current staged source differs from fixed graph: {name}")
        source_hashes[name] = staged_sha
    shutil.copyfile(a.pins / "lake-manifest.json", project / "lake-manifest.json")
    shutil.copyfile(a.pins / "lean-toolchain", project / "lean-toolchain")
    (project / "lakefile.lean").write_text(lakefile_for(names))
    (project / "module-order.txt").write_text("\n".join(ordered) + "\n")
    if inventory_names(a.audit_owners, a.audit_owners_sha256) != names:
        raise ValueError("trusted audit owners do not match the accepted source graph in order")
    advertised = inventory_names(a.audit_advertised, a.audit_advertised_sha256)
    required_public = set(ROOTS.values())
    if a.source_profile == CURRENT_PROFILE:
        required_public.add("DaggerComparator.mainA")
    if len(advertised) != spec["advertised"] or not required_public <= set(advertised):
        raise ValueError("trusted advertised-result inventory changed")
    if inventory_names(a.audit_main, a.audit_main_sha256) != list(spec["main"]):
        raise ValueError("trusted main-result audit inventory changed")
    shutil.copytree(a.cache_dotlake, project / ".lake", symlinks=False)
    (a.work / "candidate-source-hashes.json").write_text(json.dumps(source_hashes, sort_keys=True, indent=2) + "\n")
    return project


def systemd(a: argparse.Namespace, cwd: Path, command: list[str],
            log: Path, *, binary_output: bool = False, timeout: int = 21600,
            lean_path: str | None = None) -> int:
    if os.name != "posix" or os.geteuid() == 0:
        raise RuntimeError("Linux unprivileged runner required")
    common = [
        "systemd-run", "--user", "--quiet", "--wait", "--collect", "--pipe",
        "--property=RestrictAddressFamilies=~AF_UNIX",
        "--property=NoNewPrivileges=yes",
        f"--setenv=PATH={a.path_env}",
        f"--setenv=HOME={Path.home()}",
        f"--setenv=LEAN_SYSROOT={a.lean_prefix}",
        f"--working-directory={cwd}",
    ]
    if lean_path is not None:
        common.append(f"--setenv=LEAN_PATH={lean_path}")
    with log.open("wb") as out:
        proc = subprocess.run(common + command, cwd=cwd, stdout=out,
                              stderr=subprocess.PIPE, timeout=timeout, check=False)
    if proc.stderr:
        log.with_suffix(log.suffix + ".stderr").write_bytes(proc.stderr)
    if proc.returncode != 0:
        raise RuntimeError(f"{command[0]} failed ({proc.returncode}); see {log}")
    return proc.returncode


def auditor_command(a: argparse.Namespace, project: Path) -> list[str]:
    return landrun(a, project,
                   [str(a.auditor_binary), str(a.audit_owners),
                    str(a.audit_advertised), str(a.audit_main)], writable=False)


def audit_negative(a: argparse.Namespace, project: Path, name: str,
                   marker: str, *, spoof: bool = False) -> dict:
    command = auditor_command(a, project)
    prefix = ["systemd-run", "--user", "--quiet", "--wait", "--collect", "--pipe",
              "--property=RestrictAddressFamilies=~AF_UNIX",
              "--property=NoNewPrivileges=yes", f"--setenv=PATH={a.path_env}",
              f"--setenv=LEAN_SYSROOT={a.lean_prefix}",
              f"--setenv=LEAN_PATH={a.audit_lean_path}",
              f"--working-directory={project}"]
    if spoof:
        prefix.append("--setenv=BCD_AUDIT_SPOOF_PROBE=1")
    log = a.work / f"audit-negative-{name}.log"
    with log.open("wb") as output:
        result = subprocess.run(prefix + command, cwd=project, stdout=output,
                                stderr=subprocess.STDOUT, timeout=1800, check=False)
    text = log.read_text(errors="replace")
    if (result.returncode == 0 or
            "Project declaration closure depends on disallowed axiom" not in text or
            marker not in text or (spoof and "BCD_AUDIT_FORGED_JSON" in text)):
        raise RuntimeError(f"owner audit negative control failed: {log}")
    return {"case": name, "exit": result.returncode, "log_sha256": digest(log)}


def public_mutation_negative(a: argparse.Namespace, project: Path, name: str,
                             addition: str, marker: str, *, prefix: str = "",
                             spoof: bool = False,
                             public_module: str = PUBLIC_MODULE) -> dict:
    """Recompile the staged public module with one rejected test declaration.

    Run only after the positive exports. Restore both source and olean even when
    the probe fails; candidate checkout and independent Challenge stay untouched.
    """
    source = project / f"{public_module}.lean"
    olean = project / ".lake/build/lib/lean" / f"{public_module}.olean"
    backup_source = a.work / f"{name}-original-source.lean"
    backup_olean = a.work / f"{name}-original-olean.olean"
    if not source.is_file() or not olean.is_file() or olean.is_symlink():
        raise RuntimeError("public source or built olean absent before axiom probe")
    shutil.copyfile(source, backup_source)
    shutil.copyfile(olean, backup_olean)
    original_olean_sha = digest(backup_olean)
    try:
        source.write_text(prefix + backup_source.read_text() + "\n" + addition + "\n")
        compile_command = landrun(
            a, project,
            ["lake", "env", "lean", "-o", str(olean), source.name],
            writable=True,
        )
        systemd(a, project, compile_command,
                a.work / f"audit-negative-{name}-build.log", timeout=1800)
        if digest(olean) == original_olean_sha:
            raise RuntimeError("public module axiom probe did not replace the olean")
        return audit_negative(a, project, name, marker, spoof=spoof)
    finally:
        shutil.copyfile(backup_source, source)
        shutil.copyfile(backup_olean, olean)
        if digest(source) != digest(backup_source) or digest(olean) != original_olean_sha:
            raise RuntimeError("public module axiom probe failed to restore candidate build")


def external_dependency_axiom_negative(a: argparse.Namespace, project: Path,
                                       public_module: str = PUBLIC_MODULE) -> dict:
    """Check traversal into a dependency outside the frozen local-owner list."""
    name = "DaggerBCDOutsideOwnerProbe"
    source = project / f"{name}.lean"
    olean = project / ".lake/build/lib/lean" / f"{name}.olean"
    if source.exists() or olean.exists():
        raise RuntimeError("external axiom probe path already exists")
    source.write_text(f"axiom {name}.externalAx : False\n")
    try:
        compile_command = landrun(
            a, project,
            ["lake", "env", "lean", "-o", str(olean), source.name],
            writable=True,
        )
        systemd(a, project, compile_command,
                a.work / "audit-negative-external-build.log", timeout=1800)
        if not olean.is_file():
            raise RuntimeError("external axiom probe olean absent")
        return public_mutation_negative(
            a, project, "external-transitive-axiom",
            f"theorem DaggerBCDExternalProbe : False := {name}.externalAx",
            f"{name}.externalAx", prefix=f"import {name}\n",
            public_module=public_module,
        )
    finally:
        source.unlink(missing_ok=True)
        olean.unlink(missing_ok=True)


def validate_owner_audit_output(log: Path, expected_modules: list[str],
                                expected_advertised: list[str],
                                source_profile: str = RETAINED_PROFILE) -> dict:
    spec = profile_spec(source_profile)
    if source_profile == CURRENT_PROFILE:
        raw = log.read_bytes()
        try:
            text = raw.decode("utf-8")
        except UnicodeDecodeError as exc:
            raise RuntimeError(f"all-owner audit stdout is not UTF-8: {log}") from exc
        if not text.startswith("{") or not text.endswith("\n") or text.count("\n") != 1:
            raise RuntimeError(f"expected exactly one audit JSON line: {log}")
        def no_duplicate_keys(pairs: list[tuple[str, object]]) -> dict:
            obj = {}
            for key, value in pairs:
                if key in obj:
                    raise RuntimeError(f"duplicate audit JSON key: {key}")
                obj[key] = value
            return obj
        report = json.loads(text, object_pairs_hook=no_duplicate_keys)
        if (not isinstance(report, dict) or set(report) !=
                {"owned_modules", "declaration_count", "owned_declarations",
                 "declarations", "roots_by_owner", "project_axioms", "main_results"}):
            raise RuntimeError(f"all-owner audit JSON schema changed: {log}")
        stderr = log.with_suffix(log.suffix + ".stderr")
        if stderr.exists() and stderr.stat().st_size:
            raise RuntimeError(f"all-owner audit emitted stderr: {stderr}")
    else:
        reports = []
        for line in log.read_text(errors="replace").splitlines():
            if line.startswith("{"):
                try:
                    reports.append(json.loads(line))
                except json.JSONDecodeError:
                    continue
        if len(reports) != 1:
            raise RuntimeError(f"expected one all-owner audit report: {log}")
        report = reports[0]
    declarations = report.get("owned_declarations")
    metadata = report.get("declarations")
    main_results = report.get("main_results")
    advertised = set(ROOTS.values())
    if (report.get("owned_modules") != expected_modules or
            not isinstance(report.get("declaration_count"), int) or
            report["declaration_count"] <= 0 or
            not isinstance(declarations, list) or
            len(declarations) != report["declaration_count"] or
            len(declarations) != len(set(declarations)) or
            not isinstance(metadata, dict) or set(metadata) != set(expected_advertised) or
            not isinstance(main_results, dict) or
            not set(report.get("project_axioms", [])) <= set(AXIOMS) or
            set(main_results) != set(spec["main"])):
        raise RuntimeError(f"all-owner audit report failed coverage or axiom checks: {log}")
    if (report.get("roots_by_owner", {}).get(PUBLIC_MODULE, 0) < 3 or
            not advertised <= set(declarations) or
            not advertised <= set(metadata) or
            any(not isinstance(axioms, list) or not set(axioms) <= set(AXIOMS)
                for axioms in (*main_results.values(), *metadata.values()))):
        raise RuntimeError(f"public theorem audit coverage or axiom policy failed: {log}")
    if source_profile == CURRENT_PROFILE:
        by_owner = report.get("roots_by_owner")
        owned = set(declarations)
        if (len(expected_modules) != spec["modules"] or
                len(expected_advertised) != spec["advertised"] or
                type(report["declaration_count"]) is not int or
                not isinstance(by_owner, dict) or not set(by_owner) <= set(expected_modules) or
                any(type(n) is not int or n <= 0 for n in by_owner.values()) or
                sum(by_owner.values()) != report["declaration_count"] or
                by_owner.get("ProofTheoremA", 0) < 7 or
                by_owner.get("MainTheoremsA", 0) != 1 or
                "DaggerTheoremAProof.verified" not in owned or
                "DaggerComparator.mainA" not in owned or
                "DaggerComparator.mainA" not in metadata or
                any(name not in owned for name in spec["main"])):
            raise RuntimeError(f"current-2771 A audit coverage failed: {log}")
    return {"declaration_count": report["declaration_count"],
            "project_axioms": report["project_axioms"],
            "public_roots": sorted(advertised),
            "metadata_result_count": len(metadata),
            "log_sha256": digest(log)}


def landrun(a: argparse.Namespace, project: Path, payload: list[str],
            *, writable: bool) -> list[str]:
    # Deliberately omit --best-effort. Unsupported Landlock must fail closed.
    args = [str(a.landrun), "--ro", "/", "--rw", "/dev",
            "-ldd", "-add-exec", "--env", "PATH", "--env", "HOME",
            "--env", "LEAN_PATH", "--env", "LEAN_SYSROOT",
            "--env", "LEAN_ABORT_ON_PANIC", "--env", "BCD_AUDIT_SPOOF_PROBE",
            "--ro", str(project)]
    args += ["--rwx" if writable else "--ro", str(project / ".lake")]
    args += ["--rox", str(a.lean_prefix), "--rox", str(a.git_binary.parent),
             "--rox", str(a.auditor_binary.parent)]
    if not writable:
        args += ["--rox", str(a.legacy_exporter.parent)]
    return args + ["--"] + payload


def public_export_command(a: argparse.Namespace, project: Path, root: str) -> list[str]:
    """Invoke the pinned data-only exporter directly, never through candidate Lake state."""
    if not a.legacy_exporter.is_absolute():
        raise ValueError("legacy exporter path must be absolute")
    return landrun(a, project,
                   [str(a.legacy_exporter), PUBLIC_MODULE,
                    "--", root, *AXIOMS, *PRIMITIVES], writable=False)


def prove_landlock_enforced(a: argparse.Namespace, project: Path) -> None:
    """Require one allowed write and one denied write inside the same wrapper."""
    allowed = project / ".lake/landlock-allowed-probe"
    marker = project / "landlock-denial-probe"
    if marker.exists() or allowed.exists():
        raise ValueError("sandbox probe marker already exists")
    code = (
        "import pathlib,sys\n"
        "p = pathlib.Path(sys.argv[1])\n"
        "try:\n"
        "    p.write_text('probe')\n"
        "except PermissionError:\n"
        "    print('LANDLOCK_DENIED_WRITE:' + str(p), flush=True)\n"
        "    sys.exit(77)\n"
    )
    payload = ["python3", "-c", code]
    log = a.work / "landlock-denial-probe.log"
    prefix = ["systemd-run", "--user", "--quiet", "--wait", "--collect", "--pipe",
              "--property=RestrictAddressFamilies=~AF_UNIX",
              "--property=NoNewPrivileges=yes",
              f"--setenv=PATH={a.path_env}", f"--working-directory={project}"]
    with log.open("wb") as out:
        control = subprocess.run(prefix + landrun(a, project, payload + [str(allowed)], writable=True),
                                 cwd=project, stdout=out, stderr=subprocess.STDOUT,
                                 timeout=90, check=False)
        result = subprocess.run(prefix + landrun(a, project, payload + [str(marker)], writable=True),
                                cwd=project, stdout=out, stderr=subprocess.STDOUT,
                                timeout=90, check=False)
    if control.returncode != 0 or allowed.read_text() != "probe":
        raise RuntimeError(f"Landrun allowed-write control failed; see {log}")
    allowed.unlink()
    if result.returncode == 0 or marker.exists():
        raise RuntimeError(f"Landlock write-denial probe failed; see {log}")
    message = log.read_text(errors="replace")
    if f"LANDLOCK_DENIED_WRITE:{marker}" not in message:
        raise RuntimeError(f"Landrun did not demonstrate an enforced policy; see {log}")


def frozen_export(a: argparse.Namespace, rows: dict, name: str, target: Path) -> Path:
    row = rows[name]
    compressed = checked(a.frozen / row["gzip"], row["gzip_sha256"])
    with gzip.open(compressed, "rb") as source, target.open("wb") as out:
        shutil.copyfileobj(source, out)
    checked(target, row["raw_sha256"])
    if target.stat().st_size != row["raw_bytes"]:
        raise ValueError(f"raw export size mismatch: {name}")
    return target


def generic_c_export(a: argparse.Namespace, target: Path,
                     old_challenge: Path) -> tuple[dict, Path]:
    """Verify the separately accepted generic-C asset before comparing candidate output."""
    root = a.c_universe_extension
    verify_package(root, a.c_universe_manifest_sha256)
    if a.c_universe_manifest_sha256 != GENERIC_C_MANIFEST_SHA256:
        raise ValueError("unaccepted generic C manifest")
    manifest = json.loads((root / "manifest.json").read_text())
    listed = {row["path"] for row in manifest["files"]}
    actual = {p.relative_to(root).as_posix() for p in root.rglob("*") if p.is_file()}
    if actual != listed | {"manifest.json"}:
        raise ValueError("generic C asset has extra or missing files")
    extension = json.loads(checked(root / "extension.json", a.c_universe_extension_sha256).read_text())
    guard = json.loads(checked(root / "closure-guard-result.json",
                               a.c_universe_guard_result_sha256).read_text())
    if (a.c_universe_extension_sha256 != GENERIC_C_EXTENSION_SHA256 or
            a.c_universe_guard_result_sha256 != GENERIC_C_GUARD_RESULT_SHA256 or
            a.c_universe_guard_sha256 != GENERIC_C_GUARD_SHA256 or
            extension.get("kind") != "GENERIC_C_ADDITIVE_CHALLENGE_EXTENSION" or
            extension.get("old_frozen_package_unchanged") is not True or
            extension.get("old_frozen_C0_retained") is not True or
            extension.get("logical_module") != "ComparatorChallengeCOriginalMainTheoremC" or
            extension.get("source") != "sources/ComparatorChallengeCOriginalMainTheoremC.lean" or
            extension.get("source_sha256") != GENERIC_C_SOURCE_SHA256 or
            extension.get("raw_export_sha256") != GENERIC_C_RAW_SHA256 or
            extension.get("raw_export_bytes") != GENERIC_C_RAW_BYTES or
            extension.get("gzip") != "C.universal.challenge.export.gz" or
            extension.get("gzip_sha256") != GENERIC_C_GZIP_SHA256 or
            extension.get("old_raw_export_sha256") != CHALLENGE_SHA256["C"] or
            extension.get("guard_source_sha256") != GENERIC_C_GUARD_SHA256 or
            extension.get("nonroot_records_exact") != 46951 or
            extension.get("root_u0_full_record_exact") is not True or
            extension.get("project_import_exception") is not True or
            extension.get("challenge_placeholder_is_not_a_proof") is not True or
            extension.get("generic_actual_solution_replay_not_yet_run") is not True or
            extension.get("agent_review_is_not_independent_human_review") is not True or
            guard.get("kind") != "EXACT_FROZEN_C_CLOSURE_WITH_GENERIC_ROOT_ZERO_SPECIALIZATION" or
            guard.get("passed") is not True or
            guard.get("nonroot_constant_records_exact") != 46951 or
            guard.get("constant_name_sets_equal") is not True or
            guard.get("generic_root_type_exact") !=
                "DaggerChallengeOriginalMainTheoremC.Statement.{u}" or
            guard.get("generic_root_level_parameters") != ["u"] or
            guard.get("generic_root_specializes_exactly_to_frozen_C0_record") is not True or
            guard.get("old_export_sha256") != CHALLENGE_SHA256["C"] or
            guard.get("new_export_sha256") != GENERIC_C_RAW_SHA256 or
            guard.get("new_source_sha256") != GENERIC_C_SOURCE_SHA256 or
            guard.get("guard_source_sha256") != GENERIC_C_GUARD_SHA256 or
            guard.get("original_6320_modified") is not False or
            guard.get("generic_candidate_comparator_kernel_replay_passed") is not False):
        raise ValueError("generic C extension descriptor or closure evidence changed")
    checked(root / extension["source"], GENERIC_C_SOURCE_SHA256)
    checked(root / "CheckGenericCClosure.lean", a.c_universe_guard_sha256)
    if digest(old_challenge) != CHALLENGE_SHA256["C"]:
        raise ValueError("old frozen C0 Challenge changed")
    compressed = checked(root / extension["gzip"], GENERIC_C_GZIP_SHA256)
    if compressed.stat().st_size != GENERIC_C_GZIP_BYTES:
        raise ValueError("generic C gzip length changed")
    with gzip.open(compressed, "rb") as source, target.open("wb") as out:
        shutil.copyfileobj(source, out)
    checked(target, GENERIC_C_RAW_SHA256)
    if target.stat().st_size != GENERIC_C_RAW_BYTES or target.open("rb").readline().strip() != b"2.0.0":
        raise ValueError("generic C raw export length or format-2 header changed")
    return extension, target


def verify_all_frozen_exports(root: Path, rows: list[dict]) -> None:
    expected = {f"{case}.{side}.export" for case in ("B", "C", "D")
                for side in ("challenge", "solution")}
    expected |= {"control.Challenge.export", "control.Solution.export",
                 "control.Mismatch.export", "control.ForbiddenAxiom.export"}
    if len(rows) != 10 or {row["name"] for row in rows} != expected:
        raise ValueError("frozen export registry changed")
    for row in rows:
        source = checked(root / row["gzip"], row["gzip_sha256"])
        if source.stat().st_size != row["gzip_bytes"]:
            raise ValueError(f"compressed export size mismatch: {row['name']}")
        h = hashlib.sha256()
        size = 0
        with gzip.open(source, "rb") as decompressed:
            for block in iter(lambda: decompressed.read(1024 * 1024), b""):
                h.update(block)
                size += len(block)
        if size != row["raw_bytes"] or h.hexdigest() != row["raw_sha256"]:
            raise ValueError(f"raw export mismatch: {row['name']}")


def fixture_exports(a: argparse.Namespace, target: Path) -> tuple[dict, Path, Path]:
    verify_package(a.changed_definition_fixture, FIXTURE_MANIFEST_SHA256)
    fixture = json.loads(checked(a.changed_definition_fixture / "replay-case.json",
                                 FIXTURE_CASE_SHA256).read_text())
    if (fixture["name"] != "control-ChangedDefinition" or
            fixture["target"] != "DaggerBCDComparatorControl.verified" or
            fixture["protected_definition"] != "DaggerBCDComparatorControl.protectedDefinition" or
            fixture["expected_exit"] != 1 or
            fixture["expected_error"] != "Const does not match between challenge and target" or
            fixture["expected_error_constant"] != fixture["protected_definition"] or
            fixture["positive_control_uses_challenge_on_both_sides"] is not True or
            set(fixture["permitted_axioms"]) != set(AXIOMS) or
            fixture["comparator_commit"] != "14fda6a603d433dad5db83ca55f15afc91190fda" or
            fixture["checker_commit"] != "b7398199245524275543dec6113229c9bb4902e5" or
            fixture["legacy_exporter_commit"] != "bd93e5ed12fbeea19f39ec3ead659c293b2b8a95"):
        raise ValueError("changed-definition fixture metadata changed")
    rows = {row["name"]: row for row in fixture["exports"]}
    if set(rows) != {"Challenge", "Solution"}:
        raise ValueError("changed-definition fixture exports changed")
    paths = []
    for name in ("Challenge", "Solution"):
        row = rows[name]
        src = checked(a.changed_definition_fixture / f"{name}.export.gz", row["gzip_sha256"])
        dst = target / f"changed-definition-{name}.export"
        with gzip.open(src, "rb") as compressed, dst.open("wb") as raw:
            shutil.copyfileobj(compressed, raw)
        checked(dst, row["raw_sha256"])
        if dst.open("rb").readline().strip() != b"2.0.0":
            raise ValueError(f"changed-definition format-2 header absent: {name}")
        paths.append(dst)
    return fixture, paths[0], paths[1]


def compare(a: argparse.Namespace, name: str, challenge: Path, solution: Path,
            theorem: str, expected: str, expected_exit: int,
            challenge_module: str, solution_module: str) -> dict:
    config = {
        "challenge_module": challenge_module,
        "solution_module": solution_module,
        "theorem_names": [theorem],
        "permitted_axioms": list(AXIOMS),
        "enable_nanoda": False,
        "challenge_export": str(challenge),
        "solution_export": str(solution),
    }
    config_file = a.work / f"config-{name}.json"
    config_file.write_text(json.dumps(config, indent=2) + "\n")
    log = a.work / f"compare-{name}.log"
    command = [
        "systemd-run", "--user", "--quiet", "--wait", "--collect", "--pipe",
        "--property=RestrictAddressFamilies=~AF_UNIX",
        "--property=NoNewPrivileges=yes",
        f"--setenv=PATH={a.path_env}",
        f"--setenv=LEAN_PATH={a.replay_lean_path}",
        f"--setenv=DAGGER_COMPARATOR_LOCAL_CONFIG={config_file}",
        f"--working-directory={a.work}",
        str(a.landrun), "--ro", "/", "--rw", "/dev", "-ldd", "-add-exec",
        "--env", "PATH", "--env", "LEAN_PATH",
        "--env", "DAGGER_COMPARATOR_LOCAL_CONFIG",
        "--rox", str(a.lean_prefix), "--rox", str(a.replay_binary.parent),
        "--",
        str(a.replay_binary), str(config_file),
    ]
    with log.open("wb") as out:
        result = subprocess.run(command, cwd=a.work, stdout=out,
                                stderr=subprocess.STDOUT, timeout=1800, check=False)
    output = log.read_text(errors="replace")
    if result.returncode != expected_exit or expected not in output:
        raise RuntimeError(f"unexpected Comparator result in {log}")
    if expected_exit == 0 and "Lean default kernel accepts the solution" not in output:
        raise RuntimeError(f"default kernel evidence absent in {log}")
    return {"case": name, "exit": result.returncode, "log_sha256": digest(log),
            "expected_exit": expected_exit, "expected_message": expected,
            "default_kernel_acceptance_required": expected_exit == 0,
            "challenge_sha256": digest(challenge), "solution_sha256": digest(solution)}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source-profile", choices=(RETAINED_PROFILE, CURRENT_PROFILE),
                        default=RETAINED_PROFILE)
    parser.add_argument("--a-extension", type=Path)
    parser.add_argument("--a-extension-manifest-sha256")
    for key in ("candidate", "graph", "frozen", "c-universe-extension", "pins", "cache-dotlake",
                "work", "landrun", "legacy-exporter", "replay-binary",
                "lean-prefix", "git-binary", "changed-definition-fixture",
                "auditor-binary", "auditor-source", "audit-owners",
                "audit-advertised", "audit-main"):
        parser.add_argument("--" + key, type=Path, required=True)
    parser.add_argument("--replay-lean-path", required=True)
    parser.add_argument("--trusted-lean-path", required=True)
    parser.add_argument("--graph-sha256", required=True)
    for key in ("c-universe-manifest", "c-universe-extension", "c-universe-guard",
                "c-universe-guard-result"):
        parser.add_argument(f"--{key}-sha256", required=True)
    for key in ("auditor-source", "audit-owners", "audit-advertised", "audit-main"):
        parser.add_argument("--" + key + "-sha256", required=True)
    parser.add_argument("--source-revision", required=True)
    parser.add_argument("--asset-sha256", required=True)
    args = parser.parse_args()
    spec = profile_spec(args.source_profile)
    check_profile_pins(args)
    use_a_extension = a_extension_requested(args)
    a_helper = None
    if use_a_extension:
        import a_source_ci as a_helper
    args.path_env = str(args.lean_prefix / "bin") + ":" + os.environ["PATH"]
    if os.uname().sysname != "Linux" or os.geteuid() == 0:
        raise RuntimeError("real unprivileged Linux CI required")
    if not re.fullmatch(r"[0-9a-f]{40}", args.source_revision):
        raise ValueError("candidate source commit must be a full SHA-1 Git object name")
    if not re.fullmatch(r"[0-9a-f]{64}", args.asset_sha256):
        raise ValueError("trusted asset must have a full SHA256")
    if not re.fullmatch(r"[0-9a-f]{64}", args.graph_sha256):
        raise ValueError("accepted source graph must have a full trusted SHA256")
    for key in ("c_universe_manifest", "c_universe_extension", "c_universe_guard",
                "c_universe_guard_result"):
        if not re.fullmatch(r"[0-9a-f]{64}", getattr(args, f"{key}_sha256")):
            raise ValueError(f"generic C asset lacks a trusted SHA256: {key}")
    if not args.auditor_binary.is_file():
        raise ValueError("trusted separately built auditor binary is absent")
    if not args.legacy_exporter.is_absolute() or not args.legacy_exporter.is_file():
        raise ValueError("pinned legacy exporter must be an existing absolute binary")
    checked(args.auditor_source, args.auditor_source_sha256)
    verify_package(args.frozen, PACKAGE_MANIFEST_SHA256)
    a_preflight = (a_helper.validate_extension(args, sys.modules[__name__])
                   if use_a_extension else None)
    project = stage(args)
    args.audit_lean_path = str(project / ".lake/build/lib/lean") + ":" + args.trusted_lean_path
    indexes = json.loads(checked(args.frozen / "certificate-exports.json", EXPORT_INDEX_SHA256).read_text())
    verify_all_frozen_exports(args.frozen, indexes)
    rows = {row["name"]: row for row in indexes}
    case_rows = json.loads(checked(args.frozen / "replay-cases.json", CASE_INDEX_SHA256).read_text())
    cases = {row["name"]: row for row in case_rows}
    if set(cases) != {"B", "C", "D", "control-Solution", "control-Mismatch", "control-ForbiddenAxiom"}:
        raise ValueError("portable control registry changed")
    frozen = args.work / "frozen-exports"
    frozen.mkdir()
    prove_landlock_enforced(args, project)
    results = []
    # The two original 27-target negatives remain in the unchanged compare job.
    # Run the three portable package controls independently here as well.
    for label in ("control-Solution", "control-Mismatch", "control-ForbiddenAxiom"):
        row = cases[label]
        ch = frozen_export(args, rows, row["challenge"], frozen / row["challenge"])
        sol = frozen_export(args, rows, row["solution"], frozen / row["solution"])
        results.append(compare(args, label, ch, sol, row["theorem"],
                               row["expected_message"], row["expected_exit"],
                               row["challenge_module"], row["solution_module"]))
    fixture, ch, sol = fixture_exports(args, frozen)
    results.append(compare(args, "control-ChangedDefinition-unchanged", ch, ch,
                           fixture["target"],
                           "OFFICIAL_COMPARATOR_VERIFYMATCH_AND_KERNEL_REPLAY_PASSED", 0,
                           "Challenge", "Challenge"))
    results.append(compare(args, fixture["name"], ch, sol, fixture["target"],
                           fixture["expected_error"] + " '" +
                           fixture["expected_error_constant"] + "'", 1,
                           "Challenge", "Solution"))
    c_zero = cases["C"]
    c_zero_challenge = frozen_export(args, rows, c_zero["challenge"],
                                     frozen / c_zero["challenge"])
    c_zero_solution = frozen_export(args, rows, c_zero["solution"],
                                    frozen / c_zero["solution"])
    results.append(compare(args, "C-universe-zero-saved", c_zero_challenge,
                           c_zero_solution, c_zero["theorem"],
                           c_zero["expected_message"], c_zero["expected_exit"],
                           c_zero["challenge_module"], c_zero["solution_module"]))
    generic_c_case, generic_c_challenge = generic_c_export(
        args, frozen / "C.generic.challenge.export", c_zero_challenge)
    build_command = landrun(args, project,
                            ["lake", "run", "buildSequential", "module-order.txt"],
                            writable=True)
    systemd(args, project, build_command, args.work / "build-sequential.log")
    # The sequential pass is a resource-control strategy, not a substitute for
    # the repository's declared default target. Require the ordinary Lake gate.
    default_build = landrun(args, project, ["lake", "build"], writable=True)
    systemd(args, project, default_build, args.work / "build-default.log")
    owner_audit = auditor_command(args, project)
    systemd(args, project, owner_audit, args.work / "audit-all-owners.log",
            timeout=3600, lean_path=args.audit_lean_path)
    graph = json.loads(checked(args.graph, args.graph_sha256).read_text())
    audit_report = validate_owner_audit_output(
        args.work / "audit-all-owners.log",
        [row["module"] for row in graph["local_source_modules"]],
        inventory_names(args.audit_advertised, args.audit_advertised_sha256),
        args.source_profile)
    audit_controls = []
    for case in ("B", "C", "D"):
        if case == "C":
            frozen_ch = generic_c_challenge
            challenge_module = generic_c_case["logical_module"]
            case_name = "C-generic-public"
        else:
            frozen_ch = frozen_export(args, rows, f"{case}.challenge.export",
                                      frozen / f"{case}.challenge.export")
            checked(frozen_ch, CHALLENGE_SHA256[case])
            challenge_module = cases[case]["challenge_module"]
            case_name = case
        output = args.work / f"candidate-{case}.export"
        export_command = public_export_command(args, project, ROOTS[case])
        systemd(args, project, export_command, output, binary_output=True,
                timeout=1800, lean_path=args.audit_lean_path)
        if output.open("rb").readline().strip() != b"2.0.0":
            raise RuntimeError(f"legacy format-2 export missing: {output}")
        results.append(compare(args, case_name, frozen_ch, output, ROOTS[case],
                               "OFFICIAL_COMPARATOR_VERIFYMATCH_AND_KERNEL_REPLAY_PASSED", 0,
                               challenge_module,
                               PUBLIC_MODULE))
    audit_controls.extend([
        public_mutation_negative(args, project, "proof-hole",
                                 "theorem DaggerBCDSourceAuditSentinel : False := by sorry",
                                 "sorryAx", public_module=spec["last"]),
        public_mutation_negative(args, project, "unused-public-extra-axiom",
                                 "axiom DaggerBCDMainModuleProbe : False",
                                 "DaggerBCDMainModuleProbe", public_module=spec["last"]),
        external_dependency_axiom_negative(args, project, spec["last"]),
        public_mutation_negative(
            args, project, "initializer-spoof",
            "axiom DaggerBCDInitializerSpoofAxiom : False\n"
            "initialize do\n"
            "  if (← IO.getEnv \"BCD_AUDIT_SPOOF_PROBE\") == some \"1\" then\n"
            "    IO.println \"{\\\"spoof_marker\\\":\\\"BCD_AUDIT_FORGED_JSON\\\"}\"\n"
            "    IO.Process.exit 0",
            "DaggerBCDInitializerSpoofAxiom", spoof=True,
            public_module=spec["last"]),
    ])
    a_result = (a_helper.run(args, sys.modules[__name__], project, a_preflight,
                               results, audit_controls, audit_report)
                if a_preflight is not None else None)
    result = {
        "kind": "FRESH_CANDIDATE_BCD_LINUX_COMPARATOR_RESULT",
        "candidate_source_revision": args.source_revision,
        "trusted_asset_sha256": args.asset_sha256,
        "graph_sha256": args.graph_sha256,
        "auditor_source_sha256": args.auditor_source_sha256,
        "audit_inventory_sha256": {
            "owners": args.audit_owners_sha256,
            "advertised": args.audit_advertised_sha256,
            "main_results": args.audit_main_sha256,
        },
        "owner_audit": audit_report,
        "owner_audit_negative_controls": audit_controls,
        "candidate_source_hashes_sha256": digest(args.work / "candidate-source-hashes.json"),
        "candidate_public_source_sha256": digest(project / f"{PUBLIC_MODULE}.lean"),
        "landlock_write_denial_probe_passed": True,
        "candidate_source_modules": spec["modules"],
        "candidate_public_export_module": PUBLIC_MODULE,
        "generic_c_extension": {
            "case": "C-generic-public",
            "manifest_sha256": args.c_universe_manifest_sha256,
            "extension_sha256": args.c_universe_extension_sha256,
            "guard_result_sha256": args.c_universe_guard_result_sha256,
            "challenge_raw_sha256": GENERIC_C_RAW_SHA256,
            "old_C0_challenge_raw_sha256": CHALLENGE_SHA256["C"],
            "nonroot_constant_records_exact": 46951,
        },
        "tool_commits": {
            "comparator": "14fda6a603d433dad5db83ca55f15afc91190fda",
            "lean4checker": "b7398199245524275543dec6113229c9bb4902e5",
            "legacy_exporter": "bd93e5ed12fbeea19f39ec3ead659c293b2b8a95",
            "landrun": "811cfff51ceaf3d9843708aa6d22e9b84ccac8b4",
        },
        "results": results,
    }
    if args.source_profile == CURRENT_PROFILE:
        result.update({
            "kind": "CURRENT_2771_SOURCE_BCD_LINUX_CHECKS_ONLY",
            "source_profile": CURRENT_PROFILE,
            "current_source_BCD_checks": True,
            "A_Comparator_passed": False,
            "ABCD_aggregate_certificate_passed": False,
            "A_Comparator_extension_required": True,
        })
        if a_result is not None:
            result.update({
                "kind": "CURRENT_2771_ABCD_LINUX_COMPARATOR_RESULT",
                "A_Comparator_passed": True,
                "ABCD_aggregate_certificate_passed": True,
                "A_Comparator_extension_required": False,
                "A_additive_extension": a_result,
            })
    (args.work / "ci-candidate-result.json").write_text(json.dumps(result, indent=2) + "\n")


if __name__ == "__main__":
    main()
