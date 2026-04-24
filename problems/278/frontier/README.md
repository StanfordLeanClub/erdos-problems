# Frontier materials for Problem 278

This folder contains the canonical frontier-tracking artifacts for Erdős Problem #278.

## What lives here

### `current/frontier_note.md`
The canonical current **frontier note** for Problem #278.

A frontier note is the current state-of-the-frontier document for the problem. It is meant to record:

- everything the project currently treats as established at the frontier,
- the path of discovery / consolidation that led to the current branch,
- what has been promoted, demoted, or killed,
- the current best next targets,
- enough references / provenance for a skeptical reader to follow the branch from the public problem statement to the current state.

This is the main human-readable current frontier document.

### `current/frontier_visualizer.yaml`
A machine-readable summary of the current frontier note.

Its purpose is to power dashboards, summaries, and other tooling. It should summarize the current frontier in structured form, but it is **not** the authoritative mathematical exposition.

## Which file is authoritative?

For mathematical content, `current/frontier_note.md` is authoritative.

The YAML should track the frontier note. If the two disagree, fix the YAML or update both together.

## Update workflow for this folder

When the frontier materially changes:

1. update `current/frontier_note.md`;
2. update `current/frontier_visualizer.yaml` so it reflects the same current state;
3. archive the previous frontier note / YAML only if the old state is a meaningful milestone.

## Archive policy

Use `archive/` for historically meaningful checkpoints only.
Do not archive every minor refinement.
