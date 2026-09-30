"""Negative controls for the Lean axiom audit; no third-party Python packages."""

from pathlib import Path
import subprocess
import tempfile


def main() -> None:
    root = Path(__file__).resolve().parent.parent
    template = (root / "Audit.lean").read_text(encoding="utf-8")
    marker = "\n#audit_dagger_models\n"
    if template.count(marker) != 1:
        raise RuntimeError("Expected exactly one audit invocation")
    fixtures = {
        "proof hole": "theorem DaggerModels.auditSentinel : False := by sorry",
        "extra axiom": "axiom DaggerModels.auditSentinel : False",
    }
    build = root / "build"
    build.mkdir(exist_ok=True)
    with tempfile.TemporaryDirectory(prefix="audit-", dir=build) as directory:
        for index, (description, fixture) in enumerate(fixtures.items()):
            path = Path(directory) / f"Negative{index}.lean"
            source = template.replace(marker, f"\n{fixture}\n{marker}")
            path.write_text(source, encoding="utf-8")
            result = subprocess.run(
                ["lake", "env", "lean", str(path)],
                cwd=root,
                capture_output=True,
                text=True,
                timeout=180,
                check=False,
            )
            output = result.stdout + result.stderr
            expected = "DaggerModels.auditSentinel depends on disallowed axiom"
            if result.returncode == 0 or expected not in output:
                raise RuntimeError(f"Audit did not reject {description} correctly:\n{output}")
            print(f"Negative control passed: rejected {description}.", flush=True)


if __name__ == "__main__":
    main()
