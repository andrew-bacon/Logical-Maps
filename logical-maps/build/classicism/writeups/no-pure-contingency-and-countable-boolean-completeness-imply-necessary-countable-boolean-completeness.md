# No Pure Contingency ∧ Countable Boolean Completeness ⇒ □Countable Boolean Completeness

<p class='cert'>Result — Source: Misc., Lean `Classicism.Map.no_pure_contingency_and_countable_boolean_completeness_imply_necessary_countable_boolean_completeness`; produced by Claude Opus 5.5 (Anthropic), 2 October 2026, from a suggestion of Cian Dorr; recorded by Claude Opus 5.5 (Anthropic), 2 October 2026.</p>

## Premises

- **No Pure Contingency.** Each closed sentence of the pure language, if true, is necessary. This is a sentence schema, not a quantifier over propositions.
- **Countable Boolean Completeness.** Every countable property of entities of a relational type has a least upper bound in that type, where a property is countable relative to a type $\sigma$ when it injects into the finite cardinalities of properties of type $\sigma$; one instance for each $\sigma$.

## Conclusion

- **□Countable Boolean Completeness.** Necessarily, every countable property of entities of a relational type has a least upper bound in that type, with countability relative to a type $\sigma$ as in Countable Boolean Completeness; one instance for each $\sigma$.

## Proof

Every closed instance of Countable Boolean Completeness is a closed sentence of the pure language, since the principle is stated with object-language quantifiers and contains no nonlogical constant. Given Countable Boolean Completeness, each of those instances is true, and No Pure Contingency makes a true closed pure sentence necessary. So every closed instance is necessary, which is what the boxed principle asserts. Any type range and side conditions stay outside the box, as the Modal scope convention requires.

## Notes

One of the uniform family by which No Pure Contingency carries a pure principle to its boxed form.

## Revisions

- **2026-10-16** (Claude Opus 5.5 (Anthropic), at Cian Dorr's direction) — Countable Boolean Completeness now measures countability at every type $\sigma$; its instances are still closed pure sentences, so the proof is unchanged.

## Sources

- **Dorr 2 Oct** — Cian Dorr, suggestion of 2 October 2026.

<p class='cert'>Record: <code>topics/classicism/results/no-pure-contingency-and-countable-boolean-completeness-imply-necessary-countable-boolean-completeness.yaml</code></p>

## Paper references

- **Background: Classicism.** Bacon, Andrew, and Cian Dorr (2024). Classicism. In Peter Fritz and Nicholas K. Jones (eds), Higher-Order Metaphysics, Oxford University Press, pp. 109–190. The map was built from the draft dated 16 May 2023, 87 pages, which does not differ materially from the published version; all page, proposition and footnote locators in this map refer to that draft's numbering. — §2.2, p. 27. Formulation of No Pure Contingency.
