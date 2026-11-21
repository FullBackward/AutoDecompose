# Proof-graph traces from the Turing Agent project page

The paper does not print the dependency arrows, the time or the number of failures. The project
page publishes them, as one data file for each of the three research problems.

| Problem | File on the project page | SHA-256 of the file, downloaded 21 November 2026 |
|---|---|---|
| Matrix hitting points (OpenAI 116-01) | `data/traces/openai-math-116.js` | `81db7e39cb6e907ae108aa43180bf6d66131535f2a68302cbbf77c50c79d2910` |
| Hypergraph influence bound (OpenAI 186-01) | `data/traces/openai-math-186-ds.js` | `53398b94deed2c06303b729008992a3eaeff4eea61584119e50159488e05878e` |
| Random 3-SAT variance (OpenAI 235-02) | `data/traces/openai-math-235.js` | `3a272c239ff6436f84afe7051f390f3ab4e39df4ce0fc8b253c23884092c791b` |

Base address: `https://wangqy031216-cloud.github.io/turing-agent/` . The page states no licence for
these files. For that reason this folder holds only derived measures, and not the Lean statements
and proofs that the files contain.

## What each file contains

Each file assigns one JSON object. The object has three parts.

- `meta`: the title, the model, the start time, `duration` and `active` in seconds, and `stats`
  (nodes, proved, used, dropped, probes, failures, compactions, tool_calls, lessons, reviews).
- `nodes`: one record for each claim. A record has the identifier, the claim in words, the Lean
  statement, the Lean proof body, `deps` (the identifiers of the claims that this claim depends
  on), `status` (`proved` or `dropped`), the flags `used`, `reviewed` and `risk`, `route`, the
  times `t_in`, `t_ok` and `t_out` in seconds from the start, and the counts `probes` and `fails`.
- `timeline`: a list of events. This folder does not use it.

The page does not define the fields. The meanings above are the reader's inference from the names
and the values.

## Files here

- `measures.json`: for each node, the identifier, status, `deps`, flags, times, counts, the length
  of the statement in characters and the length of the proof body in lines. No Lean text.
- `trace_measures.py`: computes the graph measures and the effort figures, and writes
  `measures.json`.
- `trace_deps.py`: compares the declared `deps` with the names that each proof body contains.

To compute the figures again, download the three files into one directory with the names
`data_traces_openai-math-116.js`, `data_traces_openai-math-186-ds.js` and
`data_traces_openai-math-235.js`, then run:

```
python -I -X utf8 trace_measures.py <directory> --dump measures.json
python -I -X utf8 trace_deps.py <directory>
```

The scripts read the files as text and parse the JSON. They do not execute the files. Python 3.13
standard library only.
