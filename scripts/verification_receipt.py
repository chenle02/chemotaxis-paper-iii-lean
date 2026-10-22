#!/usr/bin/env python3
"""Bind the complete proof/checker source set to a live axiom inventory."""

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
ALLOW = ["Classical.choice", "Quot.sound", "propext"]
SCHEMA = "chemotaxis-bifurcation-source-receipt-v1"
SNAPSHOT_SCHEMA = "chemotaxis-bifurcation-source-snapshot-v1"
AUDIT_COMMIT = "46024e005996495c65ef609368e11ab39c4222e3"
PROOF_DIR = "ChemotaxisBifurcation"
BOUND_FIXED = {
    "ChemotaxisBifurcation.lean",
    "lakefile.toml",
    "lake-manifest.json",
    "lean-toolchain",
    "claims.yaml",
    "LICENSE",
    "scripts/LICENSE.axiom-audit",
    "scripts/AuditInventory.lean.txt",
}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def unique_object(pairs):
    result = {}
    for key, value in pairs:
        require(key not in result, f"duplicate JSON key: {key}")
        result[key] = value
    return result


def read_json(path):
    return json.loads(Path(path).read_text(), object_pairs_hook=unique_object)


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def bytes_digest(data):
    return hashlib.sha256(data).hexdigest()


def git_output(repo, *args):
    env = os.environ.copy()
    env["GIT_NO_REPLACE_OBJECTS"] = "1"
    return subprocess.check_output(["git", "-C", str(repo), *args], env=env)


def git_head(repo):
    return git_output(repo, "rev-parse", "HEAD").decode().strip()


def is_bound_name(name):
    return (
        name in BOUND_FIXED
        or (name.startswith(f"{PROOF_DIR}/") and name.endswith(".lean"))
        or (name.startswith("data/") and name.endswith(".json"))
        or (name.startswith("scripts/") and Path(name).suffix in (".py", ".sh", ".lean", ".sbatch"))
        or (name.startswith(".github/workflows/") and Path(name).suffix in (".yml", ".yaml"))
    )


def commit_source_hashes(repo, commit):
    resolved = git_output(repo, "rev-parse", "--verify", f"{commit}^{{commit}}").decode().strip()
    require(resolved == commit, "candidate commit does not resolve exactly")
    names = git_output(repo, "ls-tree", "-rz", "--name-only", commit).decode().split("\0")
    names = sorted(name for name in names if name and is_bound_name(name))
    return {
        name: bytes_digest(git_output(repo, "show", f"{commit}:{name}"))
        for name in names
    }


def source_files(root):
    files = set(BOUND_FIXED)
    # Use exactly the same classifier for the live tree and Git tree. Otherwise
    # adding a checker suffix can silently leave the two inventories unequal.
    for directory in (PROOF_DIR, "data", "scripts", ".github/workflows"):
        require((root / directory).is_dir(), f"missing bound directory: {directory}")
        files.update(str(p.relative_to(root)) for p in (root / directory).rglob("*")
                     if p.is_file() and is_bound_name(str(p.relative_to(root))))
    for name in files:
        path = root / name
        require(path.is_file() and not path.is_symlink(), f"missing or symlinked bound file: {name}")
    return {name: digest(root / name) for name in sorted(files)}


def source_snapshot(root=ROOT, repo=None):
    repo = root if repo is None else repo
    return {
        "schema": SNAPSHOT_SCHEMA,
        "candidate_commit": git_head(repo),
        "source_sha256": source_files(root),
    }


def audit_source_snapshot(data):
    snapshot = data.get("source_snapshot")
    require(isinstance(snapshot, dict), "audit evidence has no source snapshot")
    require(snapshot.get("schema") == SNAPSHOT_SCHEMA, "unknown source snapshot schema")
    commit = snapshot.get("candidate_commit")
    require(isinstance(commit, str) and re.fullmatch(r"[0-9a-f]{40}", commit) is not None,
            "audit source snapshot has malformed commit")
    hashes = snapshot.get("source_sha256")
    require(isinstance(hashes, dict) and hashes, "audit source snapshot has no file hashes")
    require(all(isinstance(name, str) and isinstance(value, str)
                and re.fullmatch(r"[0-9a-f]{64}", value) is not None
                for name, value in hashes.items()), "audit source snapshot has malformed file hashes")
    return snapshot


def names_once(values, field):
    require(isinstance(values, list) and values, f"empty or malformed {field}")
    require(all(isinstance(x, str) and x for x in values), f"malformed {field}")
    require(len(values) == len(set(values)), f"duplicate {field}")
    return sorted(values)


def positive_inventory(data, root):
    require(data.get("schema") == "chemotaxis-bifurcation-axiom-inventory-v1", "unknown audit schema")
    report = data["report"]
    require(report["root"] == "ChemotaxisBifurcation", "wrong audited root")
    require(report["ok"] is True and report["violations"] == [], "positive audit failed")
    require(sorted(report["allowed"]) == ALLOW, "changed axiom allowlist")
    require(set(report["axiomsUsed"]) <= set(ALLOW), "disallowed axiom")
    declarations = names_once(data["declarations"], "declarations")
    require(type(report["audited"]) is int and report["audited"] == len(declarations),
            "declaration count disagrees with inventory")
    modules = names_once(data["modules"], "modules")
    expected = ["ChemotaxisBifurcation"] + [str(p.relative_to(root).with_suffix("")).replace("/", ".")
                                             for p in (root / PROOF_DIR).rglob("*.lean")]
    require(modules == sorted(expected), "compiled module inventory differs from source modules")
    return {"declarations": declarations, "modules": modules, "axioms_used": sorted(report["axiomsUsed"]),
            "allowed_axioms": ALLOW}


def negative_control(data):
    require(data.get("schema") == "chemotaxis-bifurcation-axiom-inventory-v1", "unknown negative schema")
    report = data["report"]
    require(report["ok"] is False and report["root"] == "ChemotaxisBifurcation", "negative control passed")
    require(sorted(report["allowed"]) == ALLOW, "negative control changed allowlist")
    require(report["violations"] == [{"decl": "ChemotaxisBifurcation.auditTamper", "axioms": ["sorryAx"]}],
            "negative control did not reject the injected theorem for sorryAx")
    require("ChemotaxisBifurcation.auditTamper" in data["declarations"], "missing negative-control theorem")
    return {"declaration": "ChemotaxisBifurcation.auditTamper", "rejected_axiom": "sorryAx", "exit_code": 1}


def verify(receipt, positive, negative, root=ROOT, repo=None):
    repo = root if repo is None else repo
    require(receipt.get("schema") == SCHEMA, "unknown receipt schema")
    require(re.fullmatch(r"[0-9a-f]{40}", receipt["candidate_commit"]) is not None,
            "candidate must be a full commit hash")
    require(git_head(repo) == receipt["candidate_commit"],
            "candidate commit is not the checked-out HEAD")
    files = source_files(root)
    require(set(files) == set(receipt["source_sha256"]), "bound file set differs (missing or extra file)")
    changed = [name for name in files if files[name] != receipt["source_sha256"][name]]
    require(not changed, f"bound file hash mismatch: {changed}")
    committed = commit_source_hashes(repo, receipt["candidate_commit"])
    require(set(committed) == set(files),
            "candidate Git tree and bound source set differ (missing or extra file)")
    commit_changed = [name for name in files if committed[name] != files[name]]
    require(not commit_changed, f"working source differs from candidate Git blobs: {commit_changed}")
    live_snapshot = source_snapshot(root, repo)
    positive_snapshot = audit_source_snapshot(positive)
    negative_snapshot = audit_source_snapshot(negative)
    require(positive_snapshot == negative_snapshot,
            "positive and negative audits name different source snapshots")
    require(receipt.get("audit_source_snapshot") == live_snapshot,
            "receipt audit snapshot differs from live source")
    require(positive_snapshot == live_snapshot,
            "audit transcript is stale for the live source snapshot")
    require(receipt["audit_tool_commit"] == AUDIT_COMMIT, "changed audit tool pin")
    require(receipt["toolchain"] == (root / "lean-toolchain").read_text().strip(), "toolchain metadata drift")
    require(receipt["dependencies"] == read_json(root / "lake-manifest.json"), "dependency metadata drift")
    require(receipt["inventory"] == positive_inventory(positive, root), "live declaration inventory drift")
    require(receipt["negative_control"] == negative_control(negative), "negative-control mismatch")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest="command", required=True)
    snapshot_cmd = commands.add_parser("snapshot")
    snapshot_cmd.add_argument("--output", type=Path, required=True)
    bind = commands.add_parser("bind-audit")
    bind.add_argument("--audit", type=Path, required=True)
    bind.add_argument("--snapshot", type=Path, required=True)
    bind.add_argument("--output", type=Path, required=True)
    create = commands.add_parser("create")
    create.add_argument("--output", type=Path, required=True)
    check = commands.add_parser("verify")
    check.add_argument("receipt", type=Path)
    for cmd in (create, check):
        cmd.add_argument("--positive", type=Path, required=True)
        cmd.add_argument("--negative", type=Path, required=True)
    args = parser.parse_args()
    if args.command == "snapshot":
        args.output.write_text(json.dumps(source_snapshot(ROOT), indent=2, sort_keys=True) + "\n")
        print(f"wrote source snapshot for {len(source_files(ROOT))} files at {git_head(ROOT)}")
        return
    if args.command == "bind-audit":
        audit = read_json(args.audit)
        require("source_snapshot" not in audit, "raw audit already has a source snapshot")
        snapshot = read_json(args.snapshot)
        audit_source_snapshot({"source_snapshot": snapshot})
        audit["source_snapshot"] = snapshot
        args.output.write_text(json.dumps(audit, indent=2, sort_keys=True) + "\n")
        print(f"bound audit evidence to {len(snapshot['source_sha256'])} source files")
        return
    positive, negative = read_json(args.positive), read_json(args.negative)
    if args.command == "create":
        commit = git_head(ROOT)
        files = source_files(ROOT)
        committed = commit_source_hashes(ROOT, commit)
        require(set(committed) == set(files), "candidate Git tree and bound source set differ")
        require(committed == files, "candidate has uncommitted bound files")
        subprocess.run(["git", "diff", "--quiet", "HEAD", "--", *files], cwd=ROOT, check=True)
        positive_snapshot = audit_source_snapshot(positive)
        require(positive_snapshot == audit_source_snapshot(negative),
                "positive and negative audits name different source snapshots")
        require(positive_snapshot == source_snapshot(ROOT),
                "audit transcript is stale for the candidate source")
        receipt = {"schema": SCHEMA, "candidate_commit": commit,
                   "source_sha256": files,
                   "audit_source_snapshot": positive_snapshot,
                   "inventory": positive_inventory(positive, ROOT),
                   "negative_control": negative_control(negative),
                   "audit_tool_commit": AUDIT_COMMIT,
                   "toolchain": (ROOT / "lean-toolchain").read_text().strip(),
                   "dependencies": read_json(ROOT / "lake-manifest.json")}
        verify(receipt, positive, negative)
        args.output.write_text(json.dumps(receipt, indent=2, sort_keys=True) + "\n")
    else:
        receipt = read_json(args.receipt)
        verify(receipt, positive, negative)
    print(f"PASS: source receipt binds {len(receipt['source_sha256'])} files and "
          f"{len(receipt['inventory']['declarations'])} distinct declarations.")


if __name__ == "__main__":
    try:
        main()
    except (ValueError, KeyError, TypeError, OSError, subprocess.CalledProcessError) as error:
        print(f"FAIL: {error}", file=sys.stderr)
        sys.exit(1)
