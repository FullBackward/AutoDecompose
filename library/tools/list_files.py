"""List the files of a registered source at its pinned commit.

  py.sh list_files.py SOURCE_ID [--glob 'Archive/**/*.lean'] [--ext .lean] [--refresh]

Uses jsDelivr's keyless flat listing for GitHub; falls back to a blobless,
depth-1 git fetch of the pinned commit into a temporary directory (tree only,
no file contents), which is deleted afterwards. The listing is cached in
library/cache/<id>/files.json. Prints one "path<TAB>bytes" line per file.
"""
from __future__ import annotations

import argparse
import fnmatch
import json
import shutil
import subprocess
import tempfile

from common import CACHE, die, http_get, load_source, read_json, write_json


def via_jsdelivr(src: dict) -> list[dict]:
    url = (f"https://data.jsdelivr.com/v1/packages/gh/{src['repo_path']}@{src['commit']}"
           "?structure=flat")
    data = json.loads(http_get(url))
    return [{"path": f["name"].lstrip("/"), "bytes": f.get("size")} for f in data["files"]]


def via_git(src: dict) -> list[dict]:
    url = f"{src['base']}/{src['repo_path']}.git"
    tmp = tempfile.mkdtemp(prefix="lsfiles-")
    try:
        run = lambda *a: subprocess.run(a, cwd=tmp, capture_output=True, text=True, timeout=600)
        run("git", "init", "-q")
        run("git", "remote", "add", "origin", url)
        r = run("git", "fetch", "-q", "--depth", "1", "--filter=blob:none", "origin", src["commit"])
        if r.returncode != 0:
            die(f"git fetch failed: {r.stderr.strip()}")
        r = run("git", "ls-tree", "-r", "-l", src["commit"])
        out = []
        for line in r.stdout.splitlines():
            meta, path = line.split("\t", 1)
            size = meta.split()[3]
            out.append({"path": path, "bytes": int(size) if size.isdigit() else None})
        return out
    finally:
        shutil.rmtree(tmp, ignore_errors=True)


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("source_id")
    ap.add_argument("--glob", action="append", default=[])
    ap.add_argument("--ext", action="append", default=[])
    ap.add_argument("--refresh", action="store_true")
    a = ap.parse_args()
    src = load_source(a.source_id)
    cache = CACHE / a.source_id / "files.json"
    if cache.exists() and not a.refresh and read_json(cache)["commit"] == src["commit"]:
        files = read_json(cache)["files"]
    else:
        files = None
        if src["host"] == "github":
            try:
                files = via_jsdelivr(src)
            except Exception as e:
                print(f"# jsDelivr listing failed ({e}); falling back to git tree", flush=True)
        if files is None:
            files = via_git(src)
        write_json(cache, {"source_id": a.source_id, "commit": src["commit"], "files": files})
    for f in files:
        p = f["path"]
        if a.ext and not any(p.endswith(e) for e in a.ext):
            continue
        if a.glob and not any(fnmatch.fnmatch(p, g) for g in a.glob):
            continue
        print(f"{p}\t{f['bytes']}")


if __name__ == "__main__":
    main()
