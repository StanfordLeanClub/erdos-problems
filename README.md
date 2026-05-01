# Stanford AI for Lean Club — Erdős Problems

This repository collects research progress made by Stanford's AI for Lean club on selected Erdős problems. 

**NOTE**: current work has primarily been done in collaboration with ChatGPT-5.4-extended-thinking (via manual prompting on the GPT Plus plan, not Pro). With workflow automation and access better models, there is room for substantial improvement. 

The repo is organized **by problem**, so each problem folder can evolve semi-independently as the research frontier, paper draft, visualizer state, certificates, and Lean formalization change.

## Repository layout

- `docs/conventions/` — project-wide terminology and workflow conventions used across problem threads
- `problems/<number>/` — canonical materials for a given Erdős problem
- `tools/` — shared tooling, such as a frontier visualizer, when that tooling is ready to live in the repo

## Current problems

| Problem | Title | Status | Current center of gravity |
|---|---|---|---|
| 278 | Maximum density of congruence covers | active; paper-worthy partial progress; v12 full-union update; not a full solution | squarefree common-core graph links; exact packability; corrected full-union layer optimization; residual-core certificate frontier |

## How to read a problem folder

Each problem folder is intended to contain:

- `README.md` — human-facing overview
- `status.yaml` — machine-friendly latest-status summary
- `paper/current/` — canonical current paper draft
- `frontier/current/` — canonical current frontier note and visualizer summary
- `frontier/README.md` — local explanation of frontier materials and how to update them together
- `formalization/` — Lean sources and a map from mathematical statements to files
- `references/` — public links and lightweight reference material
- `corrections/` — correction notices for meaningful changes in the mathematical framing
- `certificates/` — finite verification artifacts and checker outputs supporting specific proof steps not yet Lean-formalized

## Recommended update philosophy

Use **stable canonical filenames** in `current/`, and put historically meaningful snapshots under `archive/`.

That keeps future updates simple: replace the current artifact, archive the old one only when the snapshot is worth preserving, and then bump the problem README + `status.yaml`.

See `docs/artifact-types.md` for artifact semantics and `docs/repo-guide.md` for the intended update workflow.
