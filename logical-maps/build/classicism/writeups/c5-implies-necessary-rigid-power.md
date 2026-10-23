# □ND ⇒ □Rigid Power

<p class='cert'>Result — Source: Misc., Lean `Classicism.Map.c5_implies_necessary_rigid_power`; produced by Claude Opus 5.5 (Anthropic), 3 October 2026, answering Cian Dorr's question whether C5 suffices; recorded by Claude Opus 5.5 (Anthropic), prompted by Cian Dorr, 3 October 2026.</p>

## Premises

- **□ND.** Necessarily, distinct things of any type are necessarily distinct.

## Conclusion

- **□Rigid Power.** Necessarily, if a relation is rigid, so is the property of being a rigid relation that entails it.

## Proof

Let $P:=\lambda X\, .\,\operatorname{Rigid}(X)\land X\le F$, for any $F$, rigid or not. Both conjuncts have the form $\Box\phi$. C5 gives S5 and BF at every world, and in S5 a formula $\Box\phi$ is non-contingent; so at every world $PX\to\Box PX$ and $\neg PX\to\Box\neg PX$. The first gives persistence. For weak inextensibility at any world, let $\forall X\, .\,PX\to\Box\mathcal XX$ and suppose $\Diamond\exists X\, .\,PX\land\neg\mathcal XX$. BF gives an $X$ with $\Diamond(PX\land\neg\mathcal XX)$, so $\Diamond PX$ and hence $PX$, so $\Box\mathcal XX$, a contradiction. So $P$ is rigid. The argument is a C-proof of Rigid Power from $\Box$ND, so necessitation and 4 give the boxed form.

## Notes

Under C5 the power property is rigid whether or not $F$ is, so the principle's content lies in settings without B, where a rigid subrelation can come into being at a world that cannot see back to the actual one. Cian Dorr expected C5 and Atomicity to be needed; Atomicity is not.

## Sources

- **Claude Opus 5.5 3 Oct** — Original argument of 3 October 2026, answering a question of Cian Dorr.

<p class='cert'>Record: <code>topics/classicism/results/c5-implies-necessary-rigid-power.yaml</code></p>

## Paper references

- **Background: Classicism.** Bacon, Andrew, and Cian Dorr (2024). Classicism. In Peter Fritz and Nicholas K. Jones (eds), Higher-Order Metaphysics, Oxford University Press, pp. 109–190. The map was built from the draft dated 16 May 2023, 87 pages, which does not differ materially from the published version; all page, proposition and footnote locators in this map refer to that draft's numbering. — §2.1, pp. 21–23. ND, B, 5 and BF under C5.
