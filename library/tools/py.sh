#!/bin/sh
# Run a library tool with the first Python 3.10+ interpreter found.
# Usage: library/tools/py.sh library/tools/<tool>.py [args...]
export PYTHONUTF8=1 PYTHONIOENCODING=utf-8
for c in python3 python "$HOME/miniconda3/python.exe" "$HOME/miniconda3/bin/python" \
         "$HOME/anaconda3/python.exe" "$HOME/anaconda3/bin/python"; do
  if command -v "$c" >/dev/null 2>&1 || [ -x "$c" ]; then
    exec "$c" "$@"
  fi
done
echo "py.sh: no Python interpreter found" >&2
exit 1
