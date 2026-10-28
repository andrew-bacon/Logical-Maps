# The propositional modal fragment of Classicism is exactly S4

Source: Andrew Bacon, *The Broadest Necessity* (2018), Theorem 5.1 and
Corollary 7.6 (§7.4). Locators refer to the author-hosted draft of 25 July
2017, pp. 24 and 40–41. Transcription and translation to the map by
OpenAI Codex, prompted by Andrew Bacon, 28 October 2026. No Lean verification.

For a propositional modal formula A, translate its propositional letters as
arbitrary type-t parameters and its box as the map's defined box, p = top.
Then

$$C\vdash A\quad\Longleftrightarrow\quad S4\vdash A.$$

Here theoremhood is schematic in the propositional parameters (equivalently,
use fresh propositional constants). This is a statement about the modal
fragment of the theory, not a claim that every individual model has exactly
S4 as its modal logic. Nor does it concern only closed pure higher-order
sentences: those do not provide arbitrary propositional valuations.

## Source and translation

The paper states the result for HFE: H with Functionality and the Rule of
Equivalence, in the full simple type hierarchy. On the map's relational types
this theory contains C. If H proves the equivalence of two formulas, the
Rule of Equivalence gives their identity; generalizing over their arguments
and applying Functionality repeatedly gives the identity of their lambda
abstractions. Thus each instance of C's Logical Equivalence schema is
available in HFE. This uses H-theoremhood, not equivalence under an optional
assumption. The paper's L coincides with the Cresswell–Suszko box p = top.

Consequently the upper bound for HFE is also an upper bound for C. In the
other direction, C has K, T, 4 and necessitation, already recorded in the map.
The appendix suppresses type e only for convenience (footnote 51, p. 34);
adding a singleton individual modalized domain gives models in the map's
language without changing propositional evaluation.

## Full modalized domains and countermodel transfer

Given a pointed reflexive transitive frame (W,R,w), Definitions 7.7–7.11
construct the full constant-domain modalized model. Its propositions are
all subsets of W, with

$$p\sim_u q\quad\Longleftrightarrow\quad p\cap R(u)=q\cap R(u).$$

Function spaces contain all maps preserving these equivalences at every
world. Propositional connectives are the Boolean operations. Proposition
7.4 identifies Leibniz equality with the modalized equivalence, so the
defined box has precisely the Kripke truth condition. Corollary 7.6 then
transfers arbitrary valuations by induction on modal formulas.

For each A not provable in S4, take a reflexive transitive Kripke
countermodel for A and apply this construction. The resulting model of
HFE, hence of C on the relational types, refutes A. This is the general
family result; the concrete two-world entry illustrates it for B. An
arbitrary nonsymmetric frame need not refute every S4 non-theorem.

Nonlogical relational constants not used for propositional parameters may
be interpreted as top. Parameters used to test a formula range freely over
propositions; the top convention in the concrete model records does not
restrict those assignments.
