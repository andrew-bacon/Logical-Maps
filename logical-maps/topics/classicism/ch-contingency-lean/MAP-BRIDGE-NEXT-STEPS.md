# Bridge status and verification steps (28 October 2026)

This folder contains `Classicism/MathematicalContingency/MapBridge.lean`, a
source-level projection of checkpoint 140's **conditional** cardinal-CH
contingency theorem. The corresponding Logical-Maps result is
`bounded-forcing-and-rigid-naturals-imply-cardinal-ch-contingency`.

Its exact map premises are:

1. `bounded-ch-forcing-setup`: existence of the same inaccessible K,L and both
   concrete MPAt instances, the original finite boxed RC instances and three
   unboxed IC instances.
2. `necessary-lower-peano-e`: `DraftBoxInfinity e` (necessary successor
   injectivity and zero not a successor on the at-least natural numbers).
3. `rigid-lower-nat-e`: strong rigidity of `LowerNat`, **not yet derived**.

The conclusion is only `contingency-of-cardinal-ch` (`◇C_N ∧ ◇¬C_N`).
It is not structural CH for all real-number structures. Neither the
necessary real-structure construction nor the equivalence of cardinal and
structural non-contingency has been established.

## Verification distinction

- The checkpoint's existing `ClosedBoundsCH01` certificate successfully passed
  its source, axiom and import audits in the saved checkpoint-140 report.
- The new `MapBridge.lean` wrapper has received only a local **static**
  dependency check and YAML parser check. It has **not** been compiled with
  Lean here (the Lean toolchain is unavailable in this execution environment).
- The map entry is `status: proved` because the proposition follows directly
  by existential instantiation and conjunction elimination from the certified
  checkpoint theorem. Its `certificate.lean` stays `none`: it is **not** yet
  certified under the existing Logical-Maps map pipeline.

## Commands to verify with Lean and the map

From `logical-maps/topics/classicism/ch-contingency-lean/`:

```sh
lake build Classicism.MathematicalContingency.MapBridge
lake build Classicism.MathematicalContingency.Certificates.ClosedBoundsCH01
```

The first command compiles the newly added bridge. The second regenerates
or validates the specific historical certificate under this project, potentially
requiring significant resources. A full clean certificate build may still fail
on the 15 independently pending historical targets.

From `logical-maps/`:

```sh
python3 scripts/pmap.py validate classicism
```

Do **not** invoke `pmap lean-check classicism --update` to mark the bridge
`verified` yet: the standalone sources use overlapping `Classicism/`
module names and are *not* part of the map's `lean_lib` or its
`Classicism/Map.lean`. The remaining step is a faithful theorem-to-schema
translation into the existing map's project and an exact statement wrapper.
Once done, run:

```sh
python3 scripts/pmap.py lean-check classicism --update
python3 scripts/pmap.py validate classicism
```

Only then set the map's verified metadata (via `--update`, never manually).
