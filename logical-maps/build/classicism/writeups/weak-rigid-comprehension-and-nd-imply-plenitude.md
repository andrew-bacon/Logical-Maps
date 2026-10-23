# Weak Rigid Comprehension ∧ ND ⇒ Plenitude

<p class='cert'>Result — Source: Classicism (2024), Lean `Classicism.Map.weak_rigid_comprehension_and_nd_imply_plenitude`; produced by Andrew Bacon and Cian Dorr; recorded by OpenAI Codex (GPT-6), prompted by Cian Dorr, 17 September 2026.</p>

## Premises

- **Weak Rigid Comprehension.** Every relation, including a proposition, is coextensive with a weakly rigid one, that is, with one that is weakly persistent and weakly inextensible.
- **ND.** Distinct things of any type are necessarily distinct.

## Conclusion

- **Plenitude.** Every total single-valued binary relation is represented by an operation. Its output type is relational, as required by the type system.

## Proof

For functional U with propositional output, choose a weakly rigid coextension $U^*$ and put $Zy=\forall p\, .\,(U^*y)p\to p$. If Uxq, weak persistence makes $(U^*x)q$ necessary, so Zx entails q. Functionality, NI and ND make every $U^*$-pair necessarily either have a different first coordinate or have second coordinate q. Weak inextensibility combines this into necessary uniqueness at x, which gives q entails Zx. Thus Zx=q and Z represents U. The source extends this construction pointwise to every relational relational output type.

## Notes

Stated in the source with Rigid Comprehension (Proposition 2.16); its proof uses only the weak persistence and the weak inextensibility of the coextension at the evaluation point, so Weak Rigid Comprehension suffices (observed by Cian Dorr, 11 October 2026; the Lean proof, which used rigidity only through those two facts, was adjusted to match). With the recorded plenitude-r-implies-distinctness-necessary-r, Plenitude is at least as strong as ND, and this record makes ND with Weak Rigid Comprehension sufficient for it.

## Revisions

- **2026-10-11** (Claude Opus 5.5 (Anthropic), at Cian Dorr's direction) — Premise weakened from Rigid Comprehension to Weak Rigid Comprehension, the source's proof using only weak persistence and weak inextensibility; the record's id changed with it (formerly rigid-comprehension-and-nd-imply-plenitude), and the proof text says "weakly rigid" and "weak" where it said "rigid", "persistence" and "inextensibility".

## Sources

- **Classicism** — Andrew Bacon and Cian Dorr, Classicism, draft of 16 May 2023, Proposition 2.16, p. 33 and n. 49.

<p class='cert'>Record: <code>topics/classicism/results/weak-rigid-comprehension-and-nd-imply-plenitude.yaml</code></p>

## Paper references

- **Proof: Classicism.** Bacon, Andrew, and Cian Dorr (2024). Classicism. In Peter Fritz and Nicholas K. Jones (eds), Higher-Order Metaphysics, Oxford University Press, pp. 109–190. The map was built from the draft dated 16 May 2023, 87 pages, which does not differ materially from the published version; all page, proposition and footnote locators in this map refer to that draft's numbering. — Proposition 2.16, p. 33 and n. 49
