# □Transversal Choice ⇒ □Well-Ordering

<p class='cert'>Result — Source: Misc., Lean `Classicism.Map.necessary_transversal_choice_r_implies_necessary_well_ordering_r`; produced by Claude Opus 5.5 (Anthropic), 8 October 2026, necessitating the unboxed argument; recorded by Claude Opus 5.5 (Anthropic), 8 October 2026.</p>

## Premises

- **□Transversal Choice.** Necessarily, every equivalence relation, at any type including e, has a transversal, that is, a property with exactly one instance in each of its cells.

## Conclusion

- **□Well-Ordering.** Necessarily, every type, including e, is well-ordered by some relation.

## Proof

The arguments of transversal-choice-r-implies-zorn-r and zorn-r-implies-well-ordering-r derive the conclusion from the premises in C, with no optional hypothesis, so the corresponding implication between closed instances is a theorem of C. Necessitate it and apply K to the boxed premises. Type ranges stay outside the box.

## Sources

- **Dorr 8 Oct** — Cian Dorr, suggestion of 8 October 2026, to connect Transversal Choice, Zorn's Lemma and Well-Ordering; unboxed proof as recorded in transversal-choice-r-implies-zorn-r and zorn-r-implies-well-ordering-r.

<p class='cert'>Record: <code>topics/classicism/results/necessary-transversal-choice-r-implies-necessary-well-ordering-r.yaml</code></p>
