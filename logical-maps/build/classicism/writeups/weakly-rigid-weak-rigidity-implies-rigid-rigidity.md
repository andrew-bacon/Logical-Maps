# Weakly Rigid Weak Rigidity ⇒ Rigid Rigidity

<p class='cert'>Result — Source: Misc., Lean `Classicism.Map.weakly_rigid_weak_rigidity_implies_rigid_rigidity`; produced by Claude Opus 5.5 (Anthropic), 10 October 2026, checking a suggestion of Cian Dorr; recorded by Claude Opus 5.5 (Anthropic), prompted by Cian Dorr, 10 October 2026.</p>

## Premises

- **Weakly Rigid Weak Rigidity.** Being weakly rigid is a weakly rigid property of relations, including propositions.

## Conclusion

- **Rigid Rigidity.** Being rigid is a rigid property of relations, including propositions.

## Proof

Fix the type tuple $\bar\sigma$, with $W:=\lambda Y\, .\,\operatorname{WeaklyRigid}(Y)$ and $R:=\lambda Y\, .\,\operatorname{Rigid}(Y)$. By weakly-rigid-weak-rigidity-implies-necessary-tame-rigidity at $\bar\sigma$, and T for the converse, $W$ and $R$ are necessarily coextensive, hence identical; so $R$ is weakly rigid. The same result at the one-element tuple $(\bar\sigma t)$ gives Tame Rigidity for properties of type $(\bar\sigma t)t$, so $R$ is rigid. The argument uses the principle at two types.

## Sources

- **Dorr 10 Oct** — Cian Dorr, suggestion of 10 October 2026.

<p class='cert'>Record: <code>topics/classicism/results/weakly-rigid-weak-rigidity-implies-rigid-rigidity.yaml</code></p>

## Paper references

- **Background: Classicism.** Bacon, Andrew, and Cian Dorr (2024). Classicism. In Peter Fritz and Nicholas K. Jones (eds), Higher-Order Metaphysics, Oxford University Press, pp. 109–190. The map was built from the draft dated 16 May 2023, 87 pages, which does not differ materially from the published version; all page, proposition and footnote locators in this map refer to that draft's numbering. — §1.5, p. 16. T and 4 for the fixed background modality.
