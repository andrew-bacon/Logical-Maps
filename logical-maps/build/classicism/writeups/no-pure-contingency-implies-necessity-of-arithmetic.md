# No Pure Contingency ⇒ Necessity of Arithmetic

<p class='cert'>Result — Source: Misc., Lean `Classicism.Map.no_pure_contingency_implies_necessity_of_arithmetic`; produced by Claude Fable 5.1 (Anthropic), prompted by Cian Dorr, 20 September 2026; recorded by Claude Fable 5.1 (Anthropic), prompted by Cian Dorr, 20 September 2026.</p>

## Premises

- **No Pure Contingency.** Each closed sentence of the pure language, if true, is necessary. This is a sentence schema, not a quantifier over propositions.

## Conclusion

- **Necessity of Arithmetic.** Every arithmetical sentence is either necessarily true or necessarily false, given that possibly zero is not a successor and successor is injective on numbers, where the numbers are the finite cardinalities of properties of a type $\sigma$. One sentence for each type $\sigma$ and each arithmetical sentence at $\sigma$.

## Proof

For an arithmetical sentence $A$, both $I\to A$ and $I\to\neg A$ are closed sentences of the pure language, since $I$, $\mathbb N$, $\operatorname{Sum}$ and $\operatorname{Prod}$ are defined from logical vocabulary. Classically one of them is true, and No Pure Contingency makes a true closed pure sentence necessary, so $\Box(I\to A)\lor\Box(I\to\neg A)$.

## Notes

Immediate, and consistent with the recorded incompatibility of No Pure Contingency with Possibility Maximalism (pure), which the Necessity of Arithmetic is also incompatible with.

## Revisions

- **2026-10-16** (Claude Opus 5.5 (Anthropic), at Cian Dorr's direction) — The Necessity of Arithmetic is now a schema in the type $\sigma$ whose finite cardinalities are the numbers; $I_\sigma$, $\mathbb N_\sigma$, $\operatorname{Sum}_\sigma$ and $\operatorname{Prod}_\sigma$ are still defined from logical vocabulary, so the proof covers every instance unchanged.

## Sources

- **Fable 20 Sep** — Claude Fable 5.1 (Anthropic), prompted by Cian Dorr, 20 September 2026.
- **Classicism** — Andrew Bacon and Cian Dorr, Classicism, draft of 16 May 2023, §2.2, p. 27 (No Pure Contingency).

<p class='cert'>Record: <code>topics/classicism/results/no-pure-contingency-implies-necessity-of-arithmetic.yaml</code></p>

## Paper references

- **Background: Classicism.** Bacon, Andrew, and Cian Dorr (2024). Classicism. In Peter Fritz and Nicholas K. Jones (eds), Higher-Order Metaphysics, Oxford University Press, pp. 109–190. The map was built from the draft dated 16 May 2023, 87 pages, which does not differ materially from the published version; all page, proposition and footnote locators in this map refer to that draft's numbering. — §2.2, p. 27
