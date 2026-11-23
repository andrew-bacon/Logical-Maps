# Cardinal CH under Mathematical Possibilism

This directory replays the three closed Classicism derivations that accompany the cardinal CH map entries. The positive result uses two unboxed instances of Relational Choice. The negative result uses neither. The common hypotheses, including the particular comprehension and intensional choice instances, are explicit in the Lean statements.

| Conclusion | Source theorem in `Classicism.MathematicalContingency.FinitePower` | Closed derivation module |
| --- | --- | --- |
| Possible cardinal CH | `positive_possible_cardinalCH` | `EndpointAssembly35` |
| Possible failure of cardinal CH | `negative_possible_not_cardinalCH` | `EndpointAssembly37` |
| Cardinal CH is contingent | `cardinalCH_contingency` | `EndpointAssembly38` |

The [combined theorem](Classicism/Results/MathematicalContingency/FinitePowerCHContingency.lean) gives the precise assumptions and links the two directions through its imports. [FinitePowerSmallness.lean](Classicism/Results/MathematicalContingency/FinitePowerSmallness.lean) supplies the size criterion used by the forcing constructions.

## Replay

Use Python 3.11 or later and Lean 4.33.1. From this directory run

```sh
python3 prepare.py
lake build FinitePowerCH
```

Preparation expands the 54 compressed JSON proof-term files and verifies the SHA-256 digests of all 1,842 proof inputs. Lean's native checker checks the imported terms. The final module prints the Lean axioms of each closed derivation. Each report in the saved run contained only `propext` and `Quot.sound`. A clean replay can be lengthy. It uses this Lake project and has no dependency on site generation or the map export.

## Provenance and verification scope

Andrew Bacon supplied the forcing argument and revised Mathematical Possibilism. OpenAI Codex formalized the argument at his direction. These sources reproduce the proof dependency closure from checkpoint 151, version 349, based on Logical Maps commit `6c763e80a6e19cddba731cc742c7842dea04b3e4`. The checkpoint recorded 444 of 444 required derivations and all 1,402 planned certification modules. This directory keeps the versions of the Classicism modules used for those checks in a separate Lake project so replay does not depend on subsequent changes to the main library. The generated map-statement audit is a separate check and remains pending.

For this submission, the 1,788 Lean sources and their compiled exports were matched against the checkpoint digests. The three closed declarations were then imported with the pinned Lean toolchain and their axiom reports were reproduced. These checks reuse the compiled dependencies.
