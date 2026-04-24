# Repo context, structure, and update workflow

This document explains why the repo exists, how it is structured, and how to update it cleanly as the project frontier moves.

## Why this repo exists

The club's Erdős-problem work is no longer just a pile of chat-local artifacts. At least for Problem #278, it has become a genuine research program with four recurring outputs:

1. a **paper draft**
2. a **frontier note**
3. a **frontier visualizer summary**
4. a **Lean formalization**

Those outputs evolve at different rates, but they are tightly linked. The repo should make that linkage legible and should make future updates low-friction.

## Design principles

The structure is built around a few rules:

- organize **by problem**, not by artifact type globally
- keep **canonical current artifacts** separate from historical milestones
- keep **problem artifacts** separate from shared **tooling**
- keep one small machine-readable status file (`status.yaml`) per problem
- let each problem own its own Lean package subtree for now

This matches the actual update rhythm so far: theorem progress usually triggers a frontier-note update first, then maybe a paper sync, then maybe a formalization update, not always all at once.

## Repo structure

```text
erdos-problems/
├── README.md
├── docs/
│   ├── conventions/
│   ├── artifact-types.md
│   └── repo-guide.md
├── problems/
│   └── 278/
│       ├── README.md
│       ├── status.yaml
│       ├── paper/
│       │   ├── current/
│       │   └── archive/
│       ├── frontier/
│       │   ├── current/
│       │   └── archive/
│       ├── formalization/
│       │   ├── README.md
│       │   └── lean/
│       └── references/
└── tools/
```

## What belongs where

### `paper/current/`
The canonical current paper source and compiled PDF.

Use stable filenames:
- `erdos278_paper.tex`
- `erdos278_paper.pdf`

### `paper/archive/`
Only historically meaningful milestones.
Do **not** archive every scratch iteration.

### `frontier/current/`
The canonical current frontier note and current visualizer YAML. See `docs/artifact-types.md` and the local `frontier/README.md` for the exact semantics of these two artifacts.

### `frontier/archive/`
Older frontier notes or YAML files that are still worth preserving as checkpoints.

### `formalization/lean/`
The Lean source tree for the problem. For now this lives **inside** the problem folder because current updates are overwhelmingly problem-local.

### `formalization/README.md`
A map from mathematical content to Lean modules plus a statement of what is already formalized and what remains next.

### `status.yaml`
A small machine-readable summary of the problem's current state. This should be updated whenever the canonical current state materially changes.

## Default update workflow

Most updates should follow one of these patterns.

### 1. Frontier-only update
Use this after a new theorem, consolidation, or step-back when the paper is not being refreshed yet.

Update:
- `frontier/current/frontier_note.md`
- `frontier/current/frontier_visualizer.yaml`
- `status.yaml`
- maybe `README.md`

### 2. Paper-sync update
Use when the paper draft catches up to the frontier.

Update:
- `paper/current/erdos278_paper.tex`
- `paper/current/erdos278_paper.pdf`
- `status.yaml`
- `README.md`

Archive the previous paper only if the older version is a real milestone.

### 3. Formalization update
Use when Lean has advanced independently of the current frontier note.

Update:
- `formalization/lean/...`
- `formalization/README.md`
- `status.yaml`

Update the paper only if the prose about formalization status needs to change.

### 4. Milestone release
Use when there is a meaningful change in the state of the project, such as:
- a new theorem family
- a new center of gravity
- a new paper-worthy stage
- a formalization milestone that changes how the project should be described

Then:
- archive the old current artifact(s) if warranted
- replace the `current/` versions
- bump `status.yaml`
- update the problem README
- update the repo root README if the top-level status description changes

## Guidance for future "help me push the update" chats

When you want help preparing the next repo update, attach the newest materials you want considered, especially:

- latest paper `.tex` and, if available, `.pdf`
- latest frontier note
- latest visualizer YAML
- latest Lean snapshot or changed Lean files
- any repo-specific files that changed (for example `status.yaml` or the problem README)

Then ask for one of:
- “prepare the next repo update”
- “tell me what to archive vs replace”
- “update the repo docs to match the new frontier”
- “prepare a clean commit plan”

## Why Lean stays inside each problem folder for now

Right now, updates are mostly problem-local. A theorem advance on #278 usually touches only #278 materials:
- frontier note
- YAML
- paper
- formalization
- problem README
- status file

Keeping the Lean subtree inside `problems/278/` makes those updates coherent and easy to review in one PR. If many Erdős problems later acquire serious Lean development, a shared top-level formalization workspace may become worth revisiting.

## Artifact semantics

The filesystem layout alone is not enough. Before pushing or updating a problem folder, read `docs/artifact-types.md`. That file defines what a frontier note is, what the frontier YAML is for, how the paper draft differs from the frontier note, what `status.yaml` should do, and how `current/` differs from `archive/`.
