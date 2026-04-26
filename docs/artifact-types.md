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

- record **everything established thus far** that the project currently treats as part of the frontier;
- record the **path of discovery / path of consolidation**, so that the reader can see how the branch developed and why the current center of gravity looks the way it does;
- clearly distinguish among:
  - results that are consolidated and should be treated as current theorems,
  - promising but not yet stabilized directions,
  - ideas that were demoted or killed;
- include enough citations / references / provenance that a fresh, skeptical reader can check the branch;
- be written so that a fresh and sufficiently capable reasoner can start from the public problem statement or the public problem page and follow the document's reasoning all the way to the current frontier.

A frontier note is therefore **not** just a lab notebook entry and **not** just a theorem list. It is the canonical human-readable record of the project's current frontier on that problem.

### How to use it

Use the frontier note when you want to know:

- what the project currently claims,
- what the current best theorem families / conceptual framework are,
- what is still open,
- what the best next targets are,
- and how the project got to its current state.

### Authoritative status

For mathematical content, the frontier note is the authoritative current narrative summary unless it has been superseded by a newer current note.

## 2. Frontier visualizer YAML

A **frontier visualizer YAML** file is a machine-readable summary of the current frontier note. Its purpose is to support visualization and lightweight tooling.

It should summarize items such as:

- current frontier version / date,
- ultimate problem and current operational goal,
- central abstractions,
- proved families,
- conjectures / live theorem targets,
- killed or demoted ideas,
- best next target.

### What it is not

The YAML is **not** the authoritative mathematical exposition. It is a structured summary for tools.

### How to use it

Use the YAML when you want to:

- drive a frontier dashboard / visualizer,
- generate status summaries,
- inspect the current state programmatically,
- or compare milestone states at a high level.

### Update rule

The YAML should be updated together with the frontier note whenever the current frontier materially changes. If the YAML and the frontier note disagree, the frontier note wins and the YAML should be fixed.

## 3. Paper draft

A **paper draft** is the current research-paper presentation of the problem branch. It is not identical to the frontier note.

A paper draft should:

- present the polished theorem/story arc that is ready to be written as a paper;
- state clearly what is and is not being claimed;
- organize results for readers who are evaluating the work as research rather than as an internal frontier checkpoint;
- include background, definitions, theorem statements, proofs or proof sketches, and references in a paper-appropriate style;
- report formalization status when relevant.

### How it differs from a frontier note

A frontier note is allowed to foreground path of discovery, consolidation choices, live targets, and demotions. A paper draft is more polished and selective: it should emphasize the mathematical story the project is ready to stand behind publicly.

### How to use it

Use the paper draft when you want:

- the current polished writeup,
- something to circulate to mathematically sophisticated readers,
- the best current paper-level account of the branch.

## 4. Lean formalization

The **Lean formalization** is the machine-checked part of the project for a given problem. It should live under `problems/<number>/formalization/lean/` and include the package metadata required to build it when possible.

### What it is for

- formalizing definitions and theorems from the problem branch;
- giving a precise, machine-checked record of what has actually been verified;
- helping separate fully stabilized statements from still-informal ones.

### How to use it

Use:

- `formalization/README.md` for the theorem-to-file map and status summary;
- the Lean source tree for the actual checked development.

### Authoritative status

The Lean code is authoritative for what has actually been formalized and build-checked. It is **not** automatically authoritative for the full mathematical frontier, because the frontier may include results not yet formalized.

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

- problem number / title,
- status,
- current center of gravity,
- latest paper path,
- latest frontier note path,
- latest frontier YAML path,
- current formalization status,
- current certificate paths, if any.

### How to use it

Use this file for:

- quick status inspection,
- generating repo summaries,
- checking that the README and canonical current paths are aligned.

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

Archive a version when it marks a real milestone, such as:

- a new theorem family,
- a major reorganization of the project,
- a paper-worthy step-change,
- a formalization milestone that changes how the project should be described.

## 8. Tooling vs problem data

Keep these separate.

### Problem data

Lives inside `problems/<number>/...`.

Examples:

- paper draft files,
- frontier note,
- frontier YAML,
- Lean code for that problem,
- problem-local references,
- problem-local certificates.

### Tooling

Lives under `tools/`.

Examples:

- frontier visualizer app code,
- scripts that validate YAML files,
- scripts that generate summaries.

The visualizer app is tooling. A problem's YAML file is problem data. A certificate checker may live in the problem's `certificates/` directory if it is problem-specific, or under `tools/` if it is reusable across problems.

## 9. Practical precedence rules

When artifacts differ, use this order:

1. **Lean code** is authoritative about what has actually been formalized and build-checked.
2. **Current frontier note** is authoritative about the current human-readable frontier narrative.
3. **Current paper draft** is authoritative about the current polished paper presentation.
4. **Current certificates** are authoritative for the finite verification artifacts they explicitly certify, but not for the whole frontier narrative.
5. **Current frontier YAML** is authoritative only as a machine-readable summary, and should follow the frontier note.
6. **Archives** are historical checkpoints, not the current state.

## 10. Minimal update checklist

When the mathematical frontier moves:

- update the current frontier note;
- update the current frontier YAML;
- update `status.yaml`;
- update the problem README if the high-level description changed;
- update the paper draft if the current paper should now reflect the new frontier;
- update the formalization README if Lean status changed;
- update or add certificates if the new result depends on a finite check.
