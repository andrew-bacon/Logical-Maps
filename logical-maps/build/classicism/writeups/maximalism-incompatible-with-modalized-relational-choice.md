# Maximalism (pure) ∧ Modalized Relational Choice ⇒ ⊥

<p class='cert'>Result — Source: Misc.; produced by Cian Dorr, 16 October 2026; the consistency premise verified by Claude Opus 5.5 (Anthropic) in symmetric-class-reflecting-surjections; recorded by Claude Opus 5.5 (Anthropic), 16 October 2026.</p>

## Premises

- **Maximalism (pure).** Every closed pure identity not provable in C is false. The non-theorem condition is metalinguistic.
- **Modalized Relational Choice.** Every necessarily serial relation is entailed by a necessarily functional relation.

## Conclusion

- **⊥.** These premises cannot all hold together.

## Proof

Let $U:=\lambda xy\, .\,(x\ne y\land\Diamond x=y)\lor\forall z\, .\,(z\ne x\to\Box z\ne x)$, of type $e\to e\to t$. It is necessarily serial by a theorem of C: if some $y$ is contingently distinct from $x$ then $Uxy$, and otherwise $Uxx$ by the second disjunct. Modalized Relational Choice at $\sigma=\tau=e$ gives $S$ with $\Box(\operatorname{Functional}(S)\land\forall xy\, .\,Sxy\to Uxy)$. Let $P$ be the closed pure sentence $\forall x\,\exists y\,(x\ne y\land\Diamond x=y)\land\neg\exists F\, (\operatorname{Functional}(F)\land\forall xy\, .\,Fxy\to x\ne y\land\Diamond x=y)$. $P$ is consistent with C: it is true at the evaluation point of the model symmetric-class-reflecting-surjections (see its write-up). So Maximalism (pure), in its possibility form, gives $\Diamond P$. Inside the possibility, the first conjunct of $P$ makes the second disjunct of $U$ false of every individual, so $S$ is a functional relation taking each individual to one contingently distinct from it, and instantiating the second conjunct of $P$ at $F:=S$ gives a contradiction. So $\Diamond\bot$, which is false.

## Notes

Uses Modalized Relational Choice only at $\sigma=\tau=e$, and Maximalism only at the one sentence $P$, whose consistency is witnessed by a model rather than by a principle of the map.

## Sources

- **Dorr 16 Oct** — Cian Dorr, suggestion of 16 October 2026.
- **Opus 16 Oct** — Claude Opus 5.5 (Anthropic), 16 October 2026, for the model witnessing the consistency premise (symmetric-class-reflecting-surjections).

<p class='cert'>Record: <code>topics/classicism/results/maximalism-incompatible-with-modalized-relational-choice.yaml</code></p>

## Paper references

- **Background: Classicism.** Bacon, Andrew, and Cian Dorr (2024). Classicism. In Peter Fritz and Nicholas K. Jones (eds), Higher-Order Metaphysics, Oxford University Press, pp. 109–190. The map was built from the draft dated 16 May 2023, 87 pages, which does not differ materially from the published version; all page, proposition and footnote locators in this map refer to that draft's numbering. — §2.6, p. 41. Maximalist Classicism and its possibility form.
