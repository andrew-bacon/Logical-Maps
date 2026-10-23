# No Pure Contingency ⇒ Necessity of Second-Order Analysis

<p class='cert'>Result — Source: Misc.; produced by Zachary Goodsell (the connection, 23 October 2026); proof by Claude Fable 5.1 (Anthropic), prompted by Zachary Goodsell, after the proof of no-pure-contingency-implies-necessity-of-arithmetic; recorded by Claude Fable 5.1 (Anthropic), prompted by Zachary Goodsell, 23 October 2026.</p>

## Premises

- **No Pure Contingency.** Each closed sentence of the pure language, if true, is necessary. This is a sentence schema, not a quantifier over propositions.

## Conclusion

- **Necessity of Second-Order Analysis.** Every second-order analytical sentence is either true in every real number structure in every possible world or false in every real number structure in every possible world. One sentence for each type $\sigma$ and each second-order analytical sentence.

## Proof

Fix a type $\sigma$ and a second-order analytical sentence $A$. The sentences $\forall\mathfrak R(\operatorname{Real}_\sigma\mathfrak R\to A(\mathfrak R))$ and $\forall\mathfrak R(\operatorname{Real}_\sigma\mathfrak R\to\neg A(\mathfrak R))$ are closed sentences of the pure language, every notion in them being defined by abstraction, so No Pure Contingency makes each necessary if true. One of them is true: if some real number structure at $\sigma$ falsifies $A$, then every one does, since any two are isomorphic and isomorphic structures agree on second-order analytical sentences (Huntington's theorem and Bacon's Lemma C.3, theorems of the non-modal fragment); and if none falsifies $A$, the first holds, vacuously when there is no structure at all. So one disjunct of the instance of the Necessity of Second-Order Analysis is true, hence necessary.

## Notes

With [[necessity-of-second-order-analysis-implies-necessity-of-analysis]] and [[necessity-of-second-order-analysis-implies-non-contingency-of-ch]] this gives the first-order schema and the Non-contingency of the Continuum Hypothesis from No Pure Contingency too, as [[no-pure-contingency-implies-necessity-of-arithmetic]] gives the Necessity of Arithmetic. The Fregean Axiom and Extensionality reach it through No Pure Contingency.

## Sources

- **Claude Fable 5.1 23 Oct** — Original connecting proof of 23 October 2026, in the record; the pattern is that of no-pure-contingency-implies-necessity-of-arithmetic, with Huntington's theorem supplying the disjunction.
- **Could mathematics have been different?** — Andrew Bacon, Could the truths of mathematics have been different?, draft of 9 October 2025, Appendix C.2, Lemma C.3 (categoricity and the invariance of second-order analytical sentences).

<p class='cert'>Record: <code>topics/classicism/results/no-pure-contingency-implies-necessity-of-second-order-analysis.yaml</code></p>

## Paper references

- **Proof: [Could the truths of mathematics have been different?](https://andrew-bacon.github.io/papers/Could%20mathematics%20have%20been%20different.pdf).** Bacon, Andrew (2025). Could the truths of mathematics have been different? Draft dated 9 October 2025, with online appendix; published in Philosophical Review 135(3), 2026, pp. 221–285, as cited by Barton and Goodsell. Locators refer to the draft. The full Boolean-valued construction is in appendix §B.2, pp. 7–9 of the separately paginated appendix (PDF pp. 41–43); Theorem 4.4 and its proof (Appendix C.1) and Lemma C.6 (Appendix C.2) were read directly on 19 October 2026. — Appendix C.2, Lemma C.3
