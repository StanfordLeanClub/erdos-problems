# Artifact types: what each document is, what it is for, and how to use it

This repo contains several recurring artifact types. They are related, but they are **not interchangeable**. This file explains what each one is, which one is authoritative for what purpose, and how they should be updated.

## Core principle

For each problem, the repo keeps a **canonical current state** under `current/` and a **small milestone archive** under `archive/`.

When a new result arrives, do **not** create a fresh ad hoc top-level file if the update is really the new canonical state. Instead:

1. update the canonical current artifact;
2. archive the old one only if it is a meaningful milestone; and
3. update the problem README and `status.yaml` if the high-level description changed.

## 1. Frontier note

A **frontier note** is the current state-of-the-frontier document for a given Erdős problem.

It should do all of the following:

- record everything established thus far that the project currently treats as part of the frontier;
- record the path of discovery / path of consolidation, so that the reader can see how the branch developed and why the current center of gravity looks the way it does;
- clearly distinguish among consolidated results, promising but not yet stabilized directions, and ideas that were demoted or killed;
- include enough citations / references / provenance that a fresh, skeptical reader can check the branch;
- be written so that a fresh and sufficiently capable reasoner can start from the public problem statement or problem page and follow the document's reasoning all the way to the current frontier.

A frontier note is therefore **not** just a lab notebook entry and **not** just a theorem list. It is the canonical human-readable record of the project's current frontier on that problem.

## 2. Frontier visualizer YAML

A **frontier visualizer YAML** file is a machine-readable summary of the current frontier note. Its purpose is to support visualization and lightweight tooling.

The YAML is **not** the authoritative mathematical exposition. It is a structured summary for tools.

If the YAML and the frontier note disagree, the frontier note wins and the YAML should be fixed.

## 3. Paper draft

A **paper draft** is the current research-paper presentation of the problem branch. It is not identical to the frontier note.

A paper draft should present the polished theorem/story arc that is ready to be written as a paper, state clearly what is and is not being claimed, and organize results for readers who are evaluating the work as research rather than as an internal frontier checkpoint.

## 4. Lean formalization

The **Lean formalization** is the machine-checked part of the project for a given problem. It should live under `problems/<number>/formalization/lean/` and include the package metadata required to build it when possible.

The Lean code is authoritative for what has actually been formalized and build-checked. It is not automatically authoritative for the full mathematical frontier, because the frontier may include results not yet formalized.

## 5. Certificate

A **certificate** is a finite verification artifact supporting a specific proof step. It may be a finite case table, checker output, short script, generated certificate, or human-readable record of a computation.

Certificates are used when a mathematical claim has been reduced to a finite verification problem, but that verification is not yet part of the Lean formalization.

### What it is for

- recording finite case checks;
- making computational or table-based proof steps reproducible;
- separating theorem-level mathematical exposition from low-level verification details;
- marking claims as certificate-backed rather than fully Lean-formalized.

### What it is not

A certificate is not the authoritative frontier narrative; that is the frontier note.

A certificate is not automatically Lean-verified; the Lean source tree remains authoritative for what has been formally checked.

### How to use it

Use a certificate when a theorem in the frontier note or paper depends on a finite residual check or computationally generated table. The frontier note should state exactly which theorem uses the certificate and what status the certificate has.

### Update rule

When adding a certificate, also update:

- the problem README;
- `status.yaml`, if the certificate changes theorem status;
- the frontier note, if the certificate supports a new result or changes a conjecture into a certificate-backed theorem.

## 6. `status.yaml`

Each problem should have a small `status.yaml` file that acts as a machine-readable pointer to the current canonical state.

Typical fields include:

- problem number / title;
- status;
- current center of gravity;
- latest paper path;
- latest frontier note path;
- latest frontier YAML path;
- current formalization status;
- current certificate paths, if any.

## 7. `current/` vs `archive/`

This distinction is part of the workflow.

### `current/`

Contains the single canonical current artifact of that type. Use stable filenames here.

Examples:

- `paper/current/erdos278_paper.tex`
- `paper/current/erdos278_paper.pdf`
- `frontier/current/frontier_note.md`
- `frontier/current/frontier_visualizer.yaml`

### `archive/`

Contains only historically meaningful snapshots. Do **not** archive every scratch revision. Git already stores fine-grained history.

Archive a version when it marks a real milestone, such as a new theorem family, a major reorganization, a paper-worthy step-change, or a formalization milestone that changes how the project should be described.

## 8. Tooling vs problem data

Keep these separate.

Problem data lives inside `problems/<number>/...`.

Tooling lives under `tools/`.

The visualizer app is tooling. A problem's YAML file is problem data. A certificate checker may live in the problem's `certificates/` directory if it is problem-specific, or under `tools/` if it is reusable across problems.

## 9. Practical precedence rules

When artifacts differ, use this order:

1. Lean code is authoritative about what has actually been formalized and build-checked.
2. Current frontier note is authoritative about the current human-readable frontier narrative.
3. Current paper draft is authoritative about the current polished paper presentation.
4. Current certificates are authoritative for the finite verification artifacts they explicitly certify, but not for the whole frontier narrative.
5. Current frontier YAML is authoritative only as a machine-readable summary, and should follow the frontier note.
6. Archives are historical checkpoints, not the current state.

## 10. Minimal update checklist

When the mathematical frontier moves:

- update the current frontier note;
- update the current frontier YAML;
- update `status.yaml`;
- update the problem README if the high-level description changed;
- update the paper draft if the current paper should now reflect the new frontier;
- update the formalization README if Lean status changed;
- update or add certificates if the new result depends on a finite check.
