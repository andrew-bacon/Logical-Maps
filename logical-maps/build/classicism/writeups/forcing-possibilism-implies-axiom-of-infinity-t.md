# Forcing Possibilism ⇒ Axiom of Infinity (type t)

<p class='cert'>Result — Source: Could the truths of mathematics have been different? (draft); produced by Andrew Bacon (§6, the remark that Mathematical Possibilism entails the axiom of infinity); proof written out by Claude Fable 5.1 (Anthropic), prompted by Zachary Goodsell, 23 October 2026; recorded by Claude Fable 5.1 (Anthropic), prompted by Zachary Goodsell, 23 October 2026.</p>

## Premises

- **Forcing Possibilism.** Every complete Boolean algebra that is finite or has strictly fewer elements than there are propositions is isomorphic to the entailment algebra below some proposition other than top.

## Conclusion

- **Axiom of Infinity (type t).** There are not finitely many propositions. No finite cardinality holds of the universal property, so the domain of the type cannot be exhausted by finitely many steps from the empty property.

## Proof

Suppose some finite cardinality holds of the universal property of propositions, say there are exactly $N$ propositions, $q_1,\dots,q_N$ (with $N\ge2$, as $\top\ne\bot$). At type $tt$ the properties $\lambda p\, .\,p=q_{i_1}\lor\dots\lor p=q_{i_k}$, one for each subset of $\{q_1,\dots,q_N\}$, are pairwise distinct, since two of them differ at some $q_i$, and under inclusion they form a complete Boolean algebra with $2^N$ elements: a finite Boolean algebra is complete, and its carrier, order, meets and joins are given by abstraction. It is finite, hence small. Forcing Possibilism gives a proposition $p\ne\top$ whose entailment algebra is isomorphic to it, so there are at least $2^N>N$ propositions, those entailing $p$. Contradiction. Hence no finite cardinality holds of the universal property of propositions.

## Notes

The one general consequence of Forcing Possibilism the map records: the principle is about the propositions there could be below some proposition, so any model with finitely many propositions refutes it, and through this result every such model on the map does, which settles the questions whether principles true in finite models, Atomicity, ND or BF for instance, imply it. Its other verdicts on the map come from Bacon's lottery model, which has it with □Rigid Comprehension and □Intensional Choice and without Atomicity.

## Sources

- **Could mathematics have been different?** — Andrew Bacon, Could the truths of mathematics have been different?, draft of 9 October 2025, §6, p. 27, "A straightforward consequence of Mathematical Possibilism is that it entails the axiom of infinity."

<p class='cert'>Record: <code>topics/classicism/results/forcing-possibilism-implies-axiom-of-infinity-t.yaml</code></p>

## Paper references

- **Origin: [Could the truths of mathematics have been different?](https://andrew-bacon.github.io/papers/Could%20mathematics%20have%20been%20different.pdf).** Bacon, Andrew (2025). Could the truths of mathematics have been different? Draft dated 9 October 2025, with online appendix; published in Philosophical Review 135(3), 2026, pp. 221–285, as cited by Barton and Goodsell. Locators refer to the draft. The full Boolean-valued construction is in appendix §B.2, pp. 7–9 of the separately paginated appendix (PDF pp. 41–43); Theorem 4.4 and its proof (Appendix C.1) and Lemma C.6 (Appendix C.2) were read directly on 19 October 2026. — §6, p. 27. Stated there for the axiom of infinity in the form that the finite numerical quantifiers over propositions form a natural number structure; the map's Axiom of Infinity (type t) says that no finite cardinality holds of the universal property of propositions.
