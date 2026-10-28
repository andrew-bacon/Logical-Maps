# CH-contingency Lean development — checkpoint 140

This folder preserves the **source** of Andrew Bacon's CH-contingency
formalization, from the source companion to full checkpoint 140
(27 October 2026). It is a **standalone Lake project**, not an extension
of the adjacent `lean/` package. Do not merge the two sets of
`Classicism/` modules without reconciling their definitions.

## Contents

- `Classicism/MathematicalContingency/`: definitions, formalized lemmas
  and CH-contingency constructions, with associated `Certificates/`.
- `Classicism/`: the version of the Classicism foundations used by
  this development.
- `Diagnostics/`: certificate drivers and verification tests.
- `lakefile.toml` and `lean-toolchain`: self-contained build metadata.
- `CHECKPOINT-140-AUDIT.json` and `CONTINUATION-140-STATUS.md`:
  contemporaneous evidence of the checkpoint's verification status.

The much larger complete recovery ZIP also contains compiled files,
logs and build caches; those are intentionally **not** committed.

## Exact mathematical and verification status

The source checkpoint reports **728 / 743** certificate targets passing,
with 15 historical targets pending. This is a preserved report, **not**
a fresh CI result for this GitHub branch. No new Lean run is claimed
by this commit.

The theorem `natural_CH_contingency_closedBounds` proves a
**conditional** contingency of cardinal/order-type CH given the
specified forcing-possibilism instances, RC/IC instances, necessary
Peano conditions, inaccessible size bounds and, importantly,
`Rigid (@LowerNat e _)`. The checkpoint discharges the earlier
regular-open and Hartogs closed-segment premises, but **does not
derive rigidity of LowerNat** from the original principles.
It **does not construct a real-number structure**, hence does not
unconditionally prove contingency of structural CH.

`DraftBoxInfinity e` means necessarily the zero/non-successor and
successor-injectivity conditions for the inductively generated
at-least finite-cardinality quantifiers. It is **not** silently
identified with the map's axiom that there are infinitely many
individuals or its necessitation.

## Relationship to Logical-Maps

The files here are a research subproject. The established
`logical-maps/topics/classicism/lean/` project and its existing
certificates are unchanged. Map entries for the new cardinal-CH
and structural-CH comparison remain **conjectured** and
`lean: none` until the precise results have been integrated with,
and passed, Logical-Maps' `pmap lean-check classicism --update`
auditing protocol. Do not mark these entries Lean verified merely
because a related local theorem had a certificate.

To check the standalone project, install the pinned Lean version
and run its declared `lake` targets from this directory. 
The checkpoint's `Checked` and `VerifiedCheckpoint` targets
previously succeeded with cached dependencies; this publication
does not establish a clean full rebuild.
