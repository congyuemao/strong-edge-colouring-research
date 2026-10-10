"""Build or verify a research archive without executing any research program."""
from __future__ import annotations

import ast
from collections import Counter
import hashlib
import json
import os
from pathlib import Path
import re
import sys
from urllib.parse import unquote

ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / "research"
ARCHIVE = ROOT / "archive"
SNAPSHOT = ARCHIVE / "research_source_manifest.json"
MANIFEST = ARCHIVE / "MANIFEST.json"
REPORT = ARCHIVE / "packaging_check.json"
EXCLUDED_DIRS = {".git", "__pycache__", ".venv", "venv", ".upload-local"}
SELF_EXCLUDED = {MANIFEST.relative_to(ROOT).as_posix(), REPORT.relative_to(ROOT).as_posix()}


def files():
    result = []
    for directory, subdirs, names in os.walk(ROOT):
        base = Path(directory)
        # The independently versioned Lean checkout is archived in its own repository.
        subdirs[:] = [name for name in subdirs if name not in EXCLUDED_DIRS
                      and not (base == ROOT and name == "formalization")]
        result.extend(base / name for name in names
                      if (base / name).is_file()
                      and (base / name).suffix not in {".pyc", ".pyo", ".tmp"})
    return sorted(result)


def record(p):
    raw = p.read_bytes()
    return {"path": p.relative_to(ROOT).as_posix(), "bytes": len(raw),
            "sha256": hashlib.sha256(raw).hexdigest()}


def write_json(p, value):
    p.parent.mkdir(parents=True, exist_ok=True)
    p.write_text(json.dumps(value, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")


def title(p):
    if p.suffix == ".md":
        for line in p.read_text(encoding="utf-8-sig").splitlines():
            if line.startswith("# "):
                return line[2:].replace("|", " / ").strip()
    if p.suffix == ".py":
        doc = ast.get_docstring(ast.parse(p.read_text(encoding="utf-8-sig")))
        if doc:
            return doc.splitlines()[0].replace("|", " / ").strip()
    if p.suffix == ".json":
        sibling = p.with_suffix(".py")
        return "计算结果或证书" + (f"；同名程序 {sibling.name}" if sibling.exists() else "；范围见相关研究稿")
    return "按时间累积的原研究检查点；最新状态见暂停交接"


def build_index(source_files):
    lines = ["# 全部原始研究文件索引", "", "此索引完整列出归档前已有的315个研究文件。标题由原稿第一标题或程序文档字符串提取，不替代成果登记表的审核状态。原始文件未重排或改写。", ""]
    for suffix, heading in [(".md", "证明稿与研究笔记"), (".py", "程序"),
                            (".json", "计算结果与证书"), (".txt", "原检查点")]:
        group = [p for p in source_files if p.suffix == suffix]
        lines += [f"## {heading} 共{len(group)}份", "", "| 文件 | 内容入口 |", "|---|---|"]
        lines += [f"| [{p.name}](../research/{p.name}) | {title(p)} |" for p in group]
        lines.append("")
    target = ROOT / "docs" / "FILE_INDEX.md"
    target.write_text("\n".join(lines), encoding="utf-8")


def validate_content(all_files):
    counts = Counter()
    imports = set()
    errors = []
    for p in all_files:
        try:
            if p.suffix == ".json":
                json.loads(p.read_text(encoding="utf-8-sig"))
                counts["json_files_parsed"] += 1
            elif p.suffix == ".py":
                tree = ast.parse(p.read_text(encoding="utf-8-sig"), filename=p.name)
                counts["python_files_parsed_without_execution"] += 1
                for node in ast.walk(tree):
                    if isinstance(node, ast.Import):
                        imports.update(x.name.split(".")[0] for x in node.names)
                    elif isinstance(node, ast.ImportFrom) and node.module:
                        imports.add(node.module.split(".")[0])
        except (ValueError, SyntaxError, UnicodeError) as exc:
            errors.append(f"{p.relative_to(ROOT)}: {type(exc).__name__}: {exc}")
    # Check the curated documentation; historical notes can contain old links.
    docs = [ROOT / "README.md"] + sorted((ROOT / "docs").glob("*.md"))
    for p in docs:
        for href in re.findall(r"\]\(([^)]+)\)", p.read_text(encoding="utf-8")):
            href = href.strip("<>")
            if re.match(r"[a-zA-Z]+://", href) or href.startswith("#"):
                continue
            target = (p.parent / unquote(href.split("#", 1)[0])).resolve()
            counts["local_document_links_checked"] += 1
            if not target.is_file():
                errors.append(f"broken link in {p.relative_to(ROOT)}: {href}")
    local_modules = {p.stem for p in all_files if p.suffix == ".py"}
    local_modules.update(p.name for p in ROOT.iterdir() if p.is_dir()
                         and p.name not in EXCLUDED_DIRS)
    external = sorted(imports - set(sys.stdlib_module_names) - local_modules)
    return dict(counts), external, errors


def verify_records(records):
    errors = []
    for entry in records:
        p = ROOT / entry["path"]
        if not p.is_file():
            errors.append(f"missing: {entry['path']}")
        elif record(p) != entry:
            errors.append(f"bytes or sha256 changed: {entry['path']}")
    return errors


def run(mode):
    source_files = sorted(p for p in SOURCE.iterdir() if p.is_file())
    if mode == "build":
        if not SNAPSHOT.exists():
            write_json(SNAPSHOT, {
                "date": "2026-10-09", "scope": "Unmodified original research files at user-requested pause.",
                "file_count": len(source_files),
                "total_bytes": sum(p.stat().st_size for p in source_files),
                "files": [record(p) for p in source_files],
            })
        else:
            problems = verify_records(json.loads(SNAPSHOT.read_text(encoding="utf-8"))["files"])
            if problems:
                raise SystemExit("Original snapshot changed:\n" + "\n".join(problems))
        build_index(source_files)
        entries = [record(p) for p in files() if p.relative_to(ROOT).as_posix() not in SELF_EXCLUDED]
        write_json(MANIFEST, {"date": "2026-10-09", "algorithm": "SHA-256",
                             "excluded_self_referential_files": sorted(SELF_EXCLUDED),
                             "files": entries})
    source_manifest = json.loads(SNAPSHOT.read_text(encoding="utf-8"))
    manifest = json.loads(MANIFEST.read_text(encoding="utf-8"))
    errors = verify_records(source_manifest["files"]) + verify_records(manifest["files"])
    current_source = {p.relative_to(ROOT).as_posix() for p in source_files}
    if current_source != {r["path"] for r in source_manifest["files"]}:
        errors.append("Original research file set differs from snapshot")
    expected_paths = {r["path"] for r in manifest["files"]}
    actual_paths = {p.relative_to(ROOT).as_posix() for p in files()} - SELF_EXCLUDED
    if actual_paths != expected_paths:
        errors.append("Archive file set differs from manifest")
    counts, external, content_errors = validate_content(files())
    errors.extend(content_errors)
    result = {"date": "2026-10-09", "ok": not errors,
              "scope": "Archive integrity, format, syntax and local links only; no research scripts executed.",
              "original_research_files": len(source_files),
              "original_research_bytes": source_manifest["total_bytes"],
              "manifested_files": len(manifest["files"]),
              **counts, "non_stdlib_nonlocal_import_names": external,
              "errors": errors}
    if mode == "build":
        write_json(REPORT, result)
    print(json.dumps(result, ensure_ascii=False, indent=2))
    if errors:
        raise SystemExit(1)


if __name__ == "__main__":
    if len(sys.argv) != 2 or sys.argv[1] not in {"build", "verify"}:
        raise SystemExit("Usage: python tools/package_archive.py build|verify")
    run(sys.argv[1])
