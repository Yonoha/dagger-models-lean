#!/usr/bin/env python3
"""Additive A Linux replay for the SHA-pinned current-2771 source CI profile."""

from __future__ import annotations

import gzip
import hashlib
import json
from pathlib import Path, PurePosixPath
import re
import shutil


GRAPH_SHA = "0a3af50bbf1dbb6ae6ddd5b679cb6d0120306c3f3d34777bc358cfd84859943f"
OLD_ASSET_SHA = "21111525e8bc72f2c40051f5ce13788beb94ca39c1e4e9daca739d8540f576b3"
ROOT = "DaggerComparator.mainA"
POSITIVE = ["Running Lean default kernel on solution.",
            "Lean default kernel accepts the solution",
            "OFFICIAL_COMPARATOR_VERIFYMATCH_AND_KERNEL_REPLAY_PASSED"]
A_CASES = {
    "A-normal-control": (0, POSITIVE),
    "A-positive": (0, POSITIVE),
    "A-weakened-True-negative": (1, ["uncaught exception: Challenge and solution theorem statement do not match: 'DaggerComparator.mainA'"]),
    "A-extra-axiom-negative": (1, ["uncaught exception: Illegal axiom detected: 'DaggerComparator.AExtraAxiom'"]),
    "A-changed-leftProper-negative": (1, ["uncaught exception: Const does not match between challenge and target 'DaggerTheoremAChallenge.leftProper'"]),
}
OLD_CASES = {"control-Solution", "control-Mismatch", "control-ForbiddenAxiom",
             "control-ChangedDefinition-unchanged", "control-ChangedDefinition",
             "C-universe-zero-saved", "B", "C-generic-public", "D"}
AUDIT_NEGATIVES = {"proof-hole", "unused-public-extra-axiom",
                   "external-transitive-axiom", "initializer-spoof"}
PINNED = {
    "current-source/source-graph.json": GRAPH_SHA,
    "current-audit/TrustedABCDAudit.lean": "c513a930965ed19cc6d757276b6d83675eb44992bc87c1bcaefcd8ae3365db03",
    "current-audit/owners.txt": "149da9a29e3cd8535e14acdb9e0c487c7692d4191fd5e9db97c03e1bee273aa2",
    "current-audit/advertised.txt": "1c8b6763d2dfef7e29d8c2142f7a07d919a7340ef9e77efa33c98c97ec0806eb",
    "current-audit/main-results.txt": "972cb0bee03545626e32f817aefb8a84603982f2a8e507c9ae57da01d9219b5b",
    "pins/lake-manifest.json": "1c6eb229691c7b0d1b38a574a7897e19dbe7f0bc2674d62c640fdc2e105e3c48",
    "pins/lean-toolchain": "d55ca0039a5479db5b38919d005b2c427b89b3be4f0184a20f2f4eae931f5bdb",
    "external-sources/ComparatorChallengeTheoremA.lean": "e63def08b85954c44e515c1c098dd4aa50368f0f1e99d57074e213fd244a6deb",
    "external-sources/ComparatorSolutionAWeakened.lean": "be46b25e9b145f32b95260ae07eac9b24ba0e6c5a51894c84fe64cbdd643a207",
    "external-sources/ComparatorSolutionAExtraAxiom.lean": "dd7da4738ad39329403276d8344377f7d9f6a97c8844dc7ca00e479c658f15b2",
    "changed-definition/ChallengeTheoremA.lean": "49a59fa469314b662fc34533f48c118710ce2e1886fa13c1e2b99096e1637b31",
    "changed-definition/ProofTheoremA.lean": "fd7505746ee206f2f53ab4c5c4b5ccd4eb02970041c64b5410bce0bdcb12c39b",
    "changed-definition/MainTheoremsA.lean": "fcd075451ab72dedb96b1adb0463775d6fd728ff80104e8aeaf7497c725e13d6",
    "statement-library/ChallengeTheoremA.lean": "2591c2201f9dea1f9c533878c996a89669426d89516655c475308e138ee7dfcf",
    "statement-library/ProofTheoremA.lean": "108dfb28670dbb641564f25442e5089be34e208c83fca91cf9be65d1ef303e76",
    "statement-library/MainTheoremsA.lean": "fcd075451ab72dedb96b1adb0463775d6fd728ff80104e8aeaf7497c725e13d6",
}
EXTRA_FILES = {"current-source/ChallengeTheoremA-closure.json",
               "A-frozen/A.challenge.export.gz", "evidence/selected-native-summary.json"}
FORBIDDEN = {"ProofTheoremA", "MainTheoremsA", "MainTheoremsABCD", "MainTheoremsBCD",
             "ProofActualMainTheoremB", "ProofOriginalMainTheoremC", "ProofActualMainTheoremD"}


def sha(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            h.update(block)
    return h.hexdigest()


def pinned(path: Path, expected: str, *, size: int | None = None) -> Path:
    if (path.is_symlink() or not path.is_file() or
            not re.fullmatch(r"[0-9a-f]{64}", expected) or sha(path) != expected or
            (size is not None and path.stat().st_size != size)):
        raise ValueError(f"A extension input SHA/size differs: {path}")
    return path


def closure_rows(graph: dict) -> list[dict]:
    rows = graph["local_source_modules"]
    if (graph.get("local_module_count") != 2771 or len(rows) != 2771 or
            graph.get("roots") != ["DaggerModels", "MainTheoremsABCD"] or
            graph.get("unresolved_nonstandard_imports")):
        raise ValueError("A extension full source graph differs")
    by_name = {r["module"]: r for r in rows}
    order = graph.get("topological_order")
    if len(by_name) != 2771 or len(order) != 2771 or set(order) != set(by_name):
        raise ValueError("A extension graph module order differs")
    seen, todo = set(), ["ChallengeTheoremA"]
    while todo:
        name = todo.pop()
        if name in seen:
            continue
        seen.add(name)
        todo.extend(x for x in by_name[name]["imports"] if x in by_name)
    if len(seen) != 366 or seen & FORBIDDEN:
        raise ValueError("A extension Challenge import closure differs")
    return [{key: by_name[name][key] for key in ("module", "path", "bytes", "sha256")}
            for name in order if name in seen]


def validate_summary(summary: dict, manifest: dict, raw_sha: str, raw_bytes: int) -> None:
    if (summary.get("kind") != "PORTABLE_SELECTED_NATIVE_A_EVIDENCE_MACOS_ONLY" or
            summary.get("source_graph_sha256") != GRAPH_SHA or
            summary.get("old_BCD_asset_dependency_sha256") != OLD_ASSET_SHA or
            summary.get("A_challenge_raw_export_sha256") != raw_sha or
            summary.get("A_challenge_raw_export_bytes") != raw_bytes or
            summary.get("full_2771_native_build_record_verified") is not True or
            summary.get("expanded_2771_71_8_native_audit_verified") is not True or
            summary.get("frozen_BCD_package_unchanged") is not True or
            summary.get("Linux_CI_passed") is not False or
            summary.get("publication_performed") is not False or
            not re.fullmatch(r"[0-9a-f]{64}", summary.get("native_original_receipt_sha256", "")) or
            not re.fullmatch(r"[0-9a-f]{64}", summary.get("accepted_build_receipt_sha256", "")) or
            not re.fullmatch(r"[0-9a-f]{64}", summary.get("expanded_audit_receipt_sha256", ""))):
        raise ValueError("A extension native evidence metrics differ")
    cases = summary.get("comparisons")
    expected = {"control-Solution": (0, POSITIVE),
                "control-Mismatch": (1, ["uncaught exception: Challenge and solution theorem statement do not match: 'ComparatorControl.target'"]),
                "control-ForbiddenAxiom": (1, ["uncaught exception: Illegal axiom detected: 'ComparatorControl.forbidden'"]),
                "control-ChangedDefinition-unchanged": (0, POSITIVE),
                "control-ChangedDefinition": (1, ["uncaught exception: Const does not match between challenge and target 'DaggerBCDComparatorControl.protectedDefinition'"]),
                **A_CASES}
    if (not isinstance(cases, list) or len(cases) != 10 or
            {r.get("name") for r in cases if isinstance(r, dict)} != set(expected)):
        raise ValueError("A extension native ten-case record incomplete")
    for row in cases:
        exit_code, lines = expected[row["name"]]
        if (row.get("exit") != exit_code or row.get("expected_lines") != lines or
                not re.fullmatch(r"[0-9a-f]{64}", row.get("log_sha256", ""))):
            raise ValueError(f"A extension native case differs: {row['name']}")
    if manifest.get("Linux_CI_passed") is not False or manifest.get("publication_performed") is not False:
        raise ValueError("A extension manifest falsely claims Linux/publication success")


def validate_extension(args, ci) -> dict:
    extension = args.a_extension
    if args.asset_sha256 != OLD_ASSET_SHA:
        raise ValueError("A extension requires the fixed old BCD trusted-base asset SHA")
    if (not extension.is_absolute() or extension.is_symlink() or not extension.is_dir() or
            extension.resolve() != extension or
            any(extension.is_relative_to(p.resolve()) for p in
                (args.candidate, args.frozen, args.cache_dotlake))):
        raise ValueError("A extension must be a separate trusted absolute directory")
    manifest = json.loads(pinned(extension / "manifest.json",
                                 args.a_extension_manifest_sha256).read_text())
    files = manifest.get("files")
    if (manifest.get("schema") != "dagger-A-additive-trusted-inputs/v1" or
            manifest.get("old_BCD_asset_dependency_sha256") != OLD_ASSET_SHA or
            manifest.get("source_graph_sha256") != GRAPH_SHA or
            not isinstance(files, dict) or set(files) != set(PINNED) | EXTRA_FILES):
        raise ValueError("A extension manifest schema/file set differs")
    members = list(extension.rglob("*"))
    if any(p.is_symlink() for p in members):
        raise ValueError("A extension contains symlink")
    actual = {p.relative_to(extension).as_posix() for p in members if p.is_file()}
    if actual != set(files) | {"manifest.json"}:
        raise ValueError("A extension has extra/missing files")
    for name, row in files.items():
        pp = PurePosixPath(name)
        if pp.is_absolute() or ".." in pp.parts or not isinstance(row, dict):
            raise ValueError("A extension manifest has unsafe member")
        source = extension
        for part in pp.parts:
            source = source / part
            if source.is_symlink():
                raise ValueError("A extension contains symlink")
        if type(row.get("bytes")) is not int or row["bytes"] < 0:
            raise ValueError("A extension manifest has invalid byte count")
        pinned(source, row.get("sha256", ""), size=row["bytes"])
        if name in PINNED and row["sha256"] != PINNED[name]:
            raise ValueError(f"A extension fixed source differs: {name}")
    for name, expected in (("current-source/source-graph.json", args.graph_sha256),
                           ("current-audit/TrustedABCDAudit.lean", args.auditor_source_sha256),
                           ("current-audit/owners.txt", args.audit_owners_sha256),
                           ("current-audit/advertised.txt", args.audit_advertised_sha256),
                           ("current-audit/main-results.txt", args.audit_main_sha256)):
        if files[name]["sha256"] != expected:
            raise ValueError("A extension and current source CI trusted inputs differ")
    inventories = {
        name: (extension / f"current-audit/{name}.txt").read_text().splitlines()
        for name in ("owners", "advertised", "main-results")}
    if (len(inventories["owners"]) != 2771 or
            len(inventories["advertised"]) != 71 or
            len(inventories["main-results"]) != 8 or
            "DaggerComparator.mainA" not in inventories["advertised"] or
            "DaggerComparator.mainA" not in inventories["main-results"]):
        raise ValueError("A extension 2771/71/8 metadata inventories differ")
    graph = json.loads((extension / "current-source/source-graph.json").read_text())
    closure = json.loads((extension / "current-source/ChallengeTheoremA-closure.json").read_text())
    if (closure.get("root") != "ChallengeTheoremA" or
            closure.get("source_graph_sha256") != GRAPH_SHA or
            closure.get("local_module_count") != 366 or
            closure.get("modules") != closure_rows(graph)):
        raise ValueError("A extension 366-module closure differs")
    if sha(args.graph) != GRAPH_SHA:
        raise ValueError("current source CI graph differs from A extension")
    summary = json.loads((extension / "evidence/selected-native-summary.json").read_text())
    raw_sha = summary.get("A_challenge_raw_export_sha256", "")
    raw_bytes = summary.get("A_challenge_raw_export_bytes")
    if not re.fullmatch(r"[0-9a-f]{64}", raw_sha) or type(raw_bytes) is not int or raw_bytes <= 0:
        raise ValueError("A frozen raw export metadata absent")
    with gzip.open(extension / "A-frozen/A.challenge.export.gz", "rb") as stream:
        h, size = hashlib.sha256(), 0
        first = stream.readline()
        h.update(first)
        size += len(first)
        if first.strip() != b"2.0.0":
            raise ValueError("A frozen export lacks legacy format-2 header")
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            h.update(block)
            size += len(block)
    if h.hexdigest() != raw_sha or size != raw_bytes:
        raise ValueError("A frozen raw export differs from native summary")
    validate_summary(summary, manifest, raw_sha, raw_bytes)
    return {"manifest_sha256": args.a_extension_manifest_sha256,
            "challenge_raw_sha256": raw_sha, "challenge_raw_bytes": raw_bytes,
            "native_original_receipt_sha256": summary["native_original_receipt_sha256"],
            "graph": graph, "summary": summary}


def assert_bcd_prerequisites(results: list[dict], negatives: list[dict], audit: dict) -> None:
    if (len(results) != 9 or {r.get("case") for r in results} != OLD_CASES or
            len(negatives) != 4 or {r.get("case") for r in negatives} != AUDIT_NEGATIVES or
            audit.get("metadata_result_count") != 71 or
            set(audit.get("public_roots", [])) != {"DaggerComparator.mainB",
                                                     "DaggerComparator.originalMainTheoremC",
                                                     "DaggerComparator.mainD"}):
        raise ValueError("A extension requires retained nine BCD cases, four audit negatives, and 71 metadata results")
    for row in results:
        if row.get("exit") != row.get("expected_exit"):
            raise ValueError("retained BCD result exit differs")
    for row in negatives:
        if type(row.get("exit")) is not int or row["exit"] == 0:
            raise ValueError("retained audit negative exit differs")


def snapshot_candidate(ci, project: Path, graph: dict) -> dict:
    out = {}
    for row in graph["local_source_modules"]:
        rel = Path(row["path"])
        source = project / rel
        olean = project / ".lake/build/lib/lean" / rel.with_suffix(".olean")
        ci.checked(source, row["sha256"])
        if (source.stat().st_size != row["bytes"] or olean.is_symlink() or
                not olean.is_file()):
            raise ValueError(f"A candidate source/olean missing: {row['module']}")
        out[row["module"]] = ci.digest(olean)
    return out


def sandboxed(ci, args, project: Path, case_root: Path, payload: list[str],
              *, writable: bool) -> list[str]:
    # landrun retains strict mode and project .lake read-only for every A process.
    command = ci.landrun(args, project, [], writable=False)
    if writable:
        command += ["--rw", str(case_root)]
    return command + payload


def copy_source(ci, extension: Path, relative: str, target: Path) -> Path:
    src = ci.checked(extension / relative, PINNED[relative])
    target.parent.mkdir(parents=True, exist_ok=True)
    shutil.copyfile(src, target)
    ci.checked(target, PINNED[relative])
    return target


def compile_case(ci, args, project: Path, case_root: Path, source: Path,
                 olean_dir: Path, lean_path: str, label: str) -> dict:
    olean_dir.mkdir(parents=True, exist_ok=True)
    target = olean_dir / (source.stem + ".olean")
    if target.exists():
        raise ValueError("A case olean would be overwritten")
    # Compiler initializers must not be able to alter the case sources or the
    # frozen Challenge export. Only this compile's output directory is writable.
    command = sandboxed(ci, args, project, olean_dir,
        [str(args.lean_prefix / "bin/lean"), "-R", str(source.parent),
         "-o", str(target), str(source)], writable=True)
    ci.systemd(args, source.parent, command, args.work / f"A-compile-{label}.log",
               timeout=1800, lean_path=lean_path)
    if not target.is_file() or target.is_symlink():
        raise ValueError(f"A external fixture did not compile: {label}")
    return {"label": label, "source_sha256": ci.digest(source),
            "olean_sha256": ci.digest(target),
            "log_sha256": ci.digest(args.work / f"A-compile-{label}.log")}


def export_case(ci, args, project: Path, case_root: Path, module: str,
                lean_path: str, label: str) -> tuple[Path, dict]:
    target = case_root / f"{label}.export"
    if target.exists():
        raise ValueError("A export would be overwritten")
    command = sandboxed(ci, args, project, case_root,
        [str(args.legacy_exporter), module, "--", ROOT, *ci.AXIOMS, *ci.PRIMITIVES],
        writable=False)
    ci.systemd(args, case_root, command, target, binary_output=True,
               timeout=1800, lean_path=lean_path)
    with target.open("rb") as stream:
        if stream.readline().strip() != b"2.0.0":
            raise ValueError(f"A export format-2 header absent: {label}")
    stderr = target.with_suffix(target.suffix + ".stderr")
    if stderr.exists() and stderr.stat().st_size != 0:
        raise ValueError(f"A export wrote stderr: {label}")
    return target, {"label": label, "module": module,
                    "raw_sha256": ci.digest(target), "raw_bytes": target.stat().st_size}


def compare_case(ci, args, name: str, challenge: Path, solution: Path,
                 challenge_module: str, solution_module: str) -> dict:
    code, lines = A_CASES[name]
    row = ci.compare(args, name, challenge, solution, ROOT, lines[-1], code,
                     challenge_module, solution_module)
    actual = (args.work / f"compare-{name}.log").read_text(encoding="utf-8").strip().splitlines()
    if actual != lines or row["exit"] != code:
        raise ValueError(f"A Comparator exact log/exit differs: {name}")
    row["expected_lines"] = lines
    return row


def check_frozen(ci, frozen: Path, info: dict) -> None:
    ci.checked(frozen, info["challenge_raw_sha256"])
    if frozen.stat().st_size != info["challenge_raw_bytes"]:
        raise ValueError("A frozen challenge raw length differs")


def run(args, ci, project: Path, extension_info: dict,
        retained_results: list[dict], audit_negatives: list[dict], audit_report: dict) -> dict:
    assert_bcd_prerequisites(retained_results, audit_negatives, audit_report)
    extension = args.a_extension
    info = validate_extension(args, ci)
    if {k: v for k, v in info.items() if k not in ("graph", "summary")} != {
            k: v for k, v in extension_info.items() if k not in ("graph", "summary")}:
        raise ValueError("A extension changed between preflight and replay")
    graph = info["graph"]
    before = snapshot_candidate(ci, project, graph)
    root = args.work / "A-cases"
    if root.exists():
        raise ValueError("A case directory must be fresh")
    root.mkdir()
    paths = {}
    for name in ("ComparatorChallengeTheoremA", "ComparatorSolutionAWeakened",
                 "ComparatorSolutionAExtraAxiom"):
        rel = f"external-sources/{name}.lean"
        paths[name] = copy_source(ci, extension, rel, root / "sources" / f"{name}.lean")
    for name in ("ChallengeTheoremA", "ProofTheoremA", "MainTheoremsA"):
        rel = f"changed-definition/{name}.lean"
        paths["changed-" + name] = copy_source(ci, extension, rel,
            root / "changed-sources" / f"{name}.lean")
    frozen = root / "A.frozen.challenge.export"
    with (gzip.open(extension / "A-frozen/A.challenge.export.gz", "rb") as source,
          frozen.open("xb") as target):
        shutil.copyfileobj(source, target)
    check_frozen(ci, frozen, info)

    def compare_frozen(name: str, solution: Path, solution_module: str) -> dict:
        check_frozen(ci, frozen, info)
        return compare_case(ci, args, name, frozen, solution,
                            "ComparatorChallengeTheoremA", solution_module)

    base = args.audit_lean_path
    compiles, exports, cases = [], [], []
    try:
        challenge_out = root / "challenge-oleans"
        challenge_path = str(challenge_out) + ":" + base
        compiles.append(compile_case(ci, args, project, root,
            paths["ComparatorChallengeTheoremA"], challenge_out, challenge_path,
            "ComparatorChallengeTheoremA"))
        challenge_current, row = export_case(ci, args, project, root,
            "ComparatorChallengeTheoremA", challenge_path, "A.challenge")
        exports.append(row)
        if (row["raw_sha256"] != info["challenge_raw_sha256"] or
                row["raw_bytes"] != info["challenge_raw_bytes"]):
            raise ValueError("Linux A Challenge export differs from frozen native export")
        actual, row = export_case(ci, args, project, root, "MainTheoremsA",
                                  base, "A.actual")
        exports.append(row)
        cases.append(compare_case(ci, args, "A-normal-control", actual, actual,
                                  "MainTheoremsA", "MainTheoremsA"))
        cases.append(compare_frozen("A-positive", actual, "MainTheoremsA"))
        for case, module in (("A-weakened-True-negative", "ComparatorSolutionAWeakened"),
                             ("A-extra-axiom-negative", "ComparatorSolutionAExtraAxiom")):
            out = root / (module + "-oleans")
            lean_path = str(out) + ":" + base
            compiles.append(compile_case(ci, args, project, root,
                                         paths[module], out, lean_path, module))
            exported, row = export_case(ci, args, project, root, module,
                                        lean_path, case)
            exports.append(row)
            cases.append(compare_frozen(case, exported, module))
        changed_out = root / "changed-oleans"
        changed_path = str(changed_out) + ":" + base
        for module in ("ChallengeTheoremA", "ProofTheoremA", "MainTheoremsA"):
            compiles.append(compile_case(ci, args, project, root,
                paths["changed-" + module], changed_out, changed_path,
                "changed-" + module))
        changed, row = export_case(ci, args, project, root, "MainTheoremsA",
                                   changed_path, "A.changed-leftProper")
        exports.append(row)
        cases.append(compare_frozen("A-changed-leftProper-negative", changed,
                                    "MainTheoremsA"))
        if (len(compiles) != 6 or len(exports) != 5 or len(cases) != 5 or
                {r["case"] for r in cases} != set(A_CASES)):
            raise ValueError("A Linux external fixture or Comparator case coverage differs")
        return {"manifest_sha256": args.a_extension_manifest_sha256,
                "frozen_challenge_raw_sha256": info["challenge_raw_sha256"],
                "native_original_receipt_sha256": info["native_original_receipt_sha256"],
                "compiled_external_fixtures": compiles,
                "exports": exports, "results": cases,
                "full_2771_source_and_olean_hashes_restored": True}
    finally:
        check_frozen(ci, frozen, info)
        after = snapshot_candidate(ci, project, graph)
        if after != before:
            raise RuntimeError("A external fixture changed actual 2771 source/olean hashes")
