# Modal Well-Ordering ⇒ □Intensional Choice

<p class='cert'>Result — Source: Misc., Lean `Classicism.Map.modal_well_ordering_r_implies_necessary_intensional_choice_r`; produced by Claude Opus 5.5 (Anthropic), prompted by Cian Dorr, 8 October 2026 (necessitating the unboxed argument); recorded by Claude Opus 5.5 (Anthropic), prompted by Cian Dorr, 8 October 2026.</p>

## Premises

- **Modal Well-Ordering.** Every type, including e, has a relation that is necessarily a well-order of it.

## Conclusion

- **□Intensional Choice.** Necessarily, if a property is necessarily instantiated, then some property entailing it is necessarily uniquely instantiated.

## Proof

If $\Box\operatorname{WO}(R)$, then $\Box\Box\operatorname{WO}(R)$ by 4, so necessarily some relation is necessarily a well-order: Modal Well-Ordering implies its own necessitation. The argument of [[modal-well-ordering-r-implies-intensional-choice-r]] derives Intensional Choice from Modal Well-Ordering in C, with no optional hypothesis, so the corresponding implication between closed instances is a theorem of C. Necessitate it and apply K. Type ranges stay outside the box.

## Notes

Replaces the result from the retired □Modal Well-Ordering, whose step from Modal Well-Ordering by 4 is now part of the proof.

## Sources

- **Dorr 7 Oct** — Cian Dorr, suggestion of 7 October 2026; unboxed proof as recorded in modal-well-ordering-r-implies-intensional-choice-r.

<p class='cert'>Record: <code>topics/classicism/results/modal-well-ordering-r-implies-necessary-intensional-choice-r.yaml</code></p>

## Paper references

- **Proof: Classicism.** Bacon, Andrew, and Cian Dorr (2024). Classicism. In Peter Fritz and Nicholas K. Jones (eds), Higher-Order Metaphysics, Oxford University Press, pp. 109–190. The map was built from the draft dated 16 May 2023, 87 pages, which does not differ materially from the published version; all page, proposition and footnote locators in this map refer to that draft's numbering. — §1.5, p. 17. The axiom 4.
