"""Fetch files of a registered source at its pinned commit into the cache.

  py.sh fetch_file.py SOURCE_ID PATH [PATH ...]
  py.sh fetch_file.py SOURCE_ID --from-list FILE   (one path per line)

Files land in library/cache/<id>/files/<path>, byte for byte, for searching
with grep. The cache is git-ignored and disposable: nothing in it is library
content. Prints the local path of each file fetched. Already-cached files are
not fetched again.
"""
from __future__ import annotations

import argparse
from pathlib import Path

from common import CACHE, fetch_at_commit, load_source


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("source_id")
    ap.add_argument("paths", nargs="*")
    ap.add_argument("--from-list")
    a = ap.parse_args()
    src = load_source(a.source_id)
    paths = list(a.paths)
    if a.from_list:
        paths += [l.split("\t")[0].strip() for l in Path(a.from_list).read_text().splitlines() if l.strip()]
    root = CACHE / a.source_id / "files"
    for p in paths:
        dest = root / p
        if not dest.exists():
            try:
                b = fetch_at_commit(src, p)
            except FileNotFoundError:
                print(f"missing\t{p}")
                continue
            dest.parent.mkdir(parents=True, exist_ok=True)
            dest.write_bytes(b)
        print(dest.as_posix())


if __name__ == "__main__":
    main()
