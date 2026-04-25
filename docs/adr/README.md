# Architecture Decision Records

This directory holds the `agda-algebras` **Architecture Decision Records** (ADRs): short, single-purpose documents that capture significant design decisions — the context that forced the decision, the decision itself, and the consequences we accept by taking it.

We follow a lightweight variant of [Michael Nygard's ADR format][nygard] adapted for a formalization project.  The goal is that a contributor joining the project a year from now can read the ADR index and understand *why* the library is shaped the way it is, without having to reconstruct the reasoning from commit messages and issue threads.

## Format

Each ADR is a single Markdown file named `NNN-short-kebab-title.md`, where `NNN` is a zero-padded three-digit sequence number.  Numbers are assigned in the order ADRs are *merged*, not proposed; a proposed ADR that lands after a later-numbered one simply gets the next available number.

Every ADR has the following sections, in order:

+  **Title** — a short noun phrase describing the decision.  The file title (`# ADR-NNN: ...`) should match the filename.
+  **Status** — one of `Proposed`, `Accepted`, `Deprecated`, or `Superseded by ADR-NNN`.  Include the date the status last changed.
+  **Context** — the situation that forced a decision.  State the forces in tension concretely; avoid rehearsing settled matters.
+  **Decision** — exactly what was decided, stated as an imperative ("The canonical development tree for 3.0 is `src/Setoid/`").  The decision should be extractable as a one-sentence elevator pitch.
+  **Consequences** — the effects the decision will have, positive and negative.  Be honest about the costs.  This is the section that prevents future contributors from relitigating the decision when the cost becomes visible.
+  **Alternatives considered** — the other options that were on the table and why they were not chosen.  Short.  The purpose is to reassure readers that the rejected options were seen, not to rehearse every detail.
+  **References** — links to the issues, pull requests, papers, or external discussions that informed the decision.

A template is provided in [`000-template.md`](000-template.md); copy it to start a new ADR.

## Lifecycle

+  **Proposed**: written and opened as a draft PR.  Review happens on the PR.
+  **Accepted**: the PR is merged.  The decision is in force as of the merge date.
+  **Deprecated**: the decision is no longer in force but has not been explicitly replaced.  Add a deprecation note at the top of the file and update the status; do not delete the ADR.
+  **Superseded by ADR-NNN**: a later ADR replaces this one.  Link forward to the superseding ADR and update the status; the superseding ADR links back.

ADRs are **append-only**.  Once accepted, the body text is not edited except to fix factual errors or update the status header.  If a decision changes, write a new ADR that supersedes the old one.

## Index

+  [ADR-001 — Setoid as canonical development tree for 3.0](001-setoid-as-canonical.md)
+  [ADR-002 — Classical structures layer: Σ-typed core with record-typed bundle views](002-classical-layer-design.md)
+  [ADR-003 — Cubical Agda as the canonical long-term target](003-cubical-canonical-target.md)

## When to write an ADR

Write an ADR when a decision

+  changes a structural property of the library (what's canonical, what gets deprecated, which tree work lands in),
+  commits the project to a direction that will be costly to reverse,
+  required substantive discussion among more than one person,

or whenever a contributor-facing convention is being set that a future contributor might reasonably want to challenge.  A commit message is not the right home for reasoning that needs to survive the decision.

Do not write an ADR for routine implementation choices, local refactors, or decisions that are reversible within a single PR.

[nygard]: https://cognitect.com/blog/2011/11/15/documenting-architecture-decisions
