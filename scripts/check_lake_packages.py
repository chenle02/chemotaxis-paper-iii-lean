#!/usr/bin/env python3
"""Check restored Lake Git dependencies against lake-manifest.json.

Local audit helper only.  It does not run Lean or access the network.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
from pathlib import Path, PurePosixPath
import shutil
import subprocess
import sys
import tempfile


class CheckError(RuntimeError):
    pass


def run(git: str, repo: Path, *args: str, check: bool = True) -> subprocess.CompletedProcess[str]:
    env = os.environ.copy()
    env["GIT_NO_REPLACE_OBJECTS"] = "1"
    env["GIT_OPTIONAL_LOCKS"] = "0"
    return subprocess.run(
        [git, "-C", str(repo), *args],
        check=check,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        env=env,
    )


def file_hash(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def safe_component(value: object, field: str) -> str:
    if not isinstance(value, str) or not value or value in {".", ".."} or PurePosixPath(value).name != value:
        raise CheckError(f"unsafe {field}: {value!r}")
    return value


def check_packages(root: Path, manifest_path: Path, git: str) -> dict[str, object]:
    root = root.resolve()
    manifest_path = manifest_path.resolve()
    manifest = json.loads(manifest_path.read_text())
    packages_dir_raw = manifest.get("packagesDir")
    if not isinstance(packages_dir_raw, str):
        raise CheckError("manifest packagesDir is missing")
    packages_dir_rel = PurePosixPath(packages_dir_raw)
    if packages_dir_rel.is_absolute() or ".." in packages_dir_rel.parts:
        raise CheckError("manifest packagesDir is unsafe")
    packages_dir = root.joinpath(*packages_dir_rel.parts)
    packages = manifest.get("packages")
    if not isinstance(packages, list) or not packages:
        raise CheckError("manifest packages list is empty")
    observed: dict[str, object] = {}
    for record in packages:
        if not isinstance(record, dict) or record.get("type") != "git":
            raise CheckError("every replay dependency must be a Git package")
        name = safe_component(record.get("name"), "package name")
        if name in observed:
            raise CheckError(f"duplicate package name: {name}")
        revision = record.get("rev")
        if not isinstance(revision, str) or re.fullmatch(r"[0-9a-f]{40}", revision) is None:
            raise CheckError(f"package {name} has no full revision")
        package = packages_dir / name
        if not package.is_dir() or package.is_symlink():
            raise CheckError(f"missing real package directory: {name}")
        inside = run(git, package, "rev-parse", "--is-inside-work-tree").stdout.strip()
        if inside != "true":
            raise CheckError(f"package is not a Git worktree: {name}")
        top = Path(run(git, package, "rev-parse", "--show-toplevel").stdout.strip()).resolve()
        if top != package.resolve():
            raise CheckError(f"package inherits a parent Git repository: {name}")
        head = run(git, package, "rev-parse", "HEAD").stdout.strip()
        if head != revision:
            raise CheckError(f"wrong package revision for {name}: expected {revision}, observed {head}")
        status = run(git, package, "status", "--porcelain=v1", "--untracked-files=normal").stdout
        if status:
            raise CheckError(f"dirty package source: {name}: {status.splitlines()!r}")
        tree = run(git, package, "rev-parse", "HEAD^{tree}").stdout.strip()
        observed[name] = {
            "declared_rev": revision,
            "observed_head": head,
            "observed_tree": tree,
            "source_status": "clean, including nonignored untracked files",
        }
    return {
        "schema": "chemotaxis-lake-package-check-v1",
        "manifest_sha256": file_hash(manifest_path),
        "packages_dir": packages_dir_raw,
        "packages": observed,
    }


def init_repo(path: Path, git: str, content: str) -> str:
    path.mkdir(parents=True)
    run(git, path, "init", "-q")
    run(git, path, "config", "user.name", "fixture")
    run(git, path, "config", "user.email", "fixture@example.com")
    (path / "source.txt").write_text(content)
    run(git, path, "add", "source.txt")
    run(git, path, "commit", "-qm", "fixture")
    return run(git, path, "rev-parse", "HEAD").stdout.strip()


def expect_failure(root: Path, manifest: Path, git: str, phrase: str) -> None:
    try:
        check_packages(root, manifest, git)
    except CheckError as error:
        if phrase not in str(error):
            raise AssertionError(f"expected {phrase!r}, got {error!r}") from error
    else:
        raise AssertionError(f"expected failure containing {phrase!r}")


def self_test(git: str) -> None:
    with tempfile.TemporaryDirectory(prefix="chemotaxis-lake-package-check.") as temp:
        root = Path(temp)
        package = root / ".lake/packages/demo"
        revision = init_repo(package, git, "clean\n")
        manifest = root / "lake-manifest.json"

        def write(rev: str = revision, name: str = "demo") -> None:
            manifest.write_text(json.dumps({
                "version": "fixture",
                "packagesDir": ".lake/packages",
                "packages": [{"name": name, "type": "git", "rev": rev}],
            }) + "\n")

        write()
        result = check_packages(root, manifest, git)
        assert result["packages"]["demo"]["observed_head"] == revision
        (package / "source.txt").write_text("dirty\n")
        expect_failure(root, manifest, git, "dirty package source")
        run(git, package, "checkout", "--", "source.txt")
        (package / "extra.lean").write_text("-- untracked dependency source\n")
        expect_failure(root, manifest, git, "dirty package source")
        (package / "extra.lean").unlink()
        write()
        duplicated = json.loads(manifest.read_text())
        duplicated["packages"].append(dict(duplicated["packages"][0]))
        manifest.write_text(json.dumps(duplicated))
        expect_failure(root, manifest, git, "duplicate package name")
        write("0" * 40)
        expect_failure(root, manifest, git, "wrong package revision")
        write(name="missing")
        expect_failure(root, manifest, git, "missing real package directory")
    print("PASS: clean dependency accepted; dirty, untracked, duplicate, wrong-revision, and missing fixtures rejected")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--git", default=shutil.which("git") or "git")
    parser.add_argument("--self-test", action="store_true")
    parser.add_argument("--root", type=Path)
    parser.add_argument("--manifest", type=Path)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    try:
        if args.self_test:
            self_test(args.git)
            return 0
        if args.root is None or args.manifest is None or args.output is None:
            parser.error("--root, --manifest, and --output are required unless --self-test is used")
        result = check_packages(args.root, args.manifest, args.git)
        temporary = args.output.with_suffix(args.output.suffix + ".tmp")
        temporary.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
        os.replace(temporary, args.output)
        print(f"PASS: {len(result['packages'])} Lake Git packages match full revisions and clean source")
        return 0
    except (CheckError, OSError, subprocess.CalledProcessError, json.JSONDecodeError) as error:
        print(f"FAIL: {error}", file=sys.stderr)
        return 65


if __name__ == "__main__":
    raise SystemExit(main())
