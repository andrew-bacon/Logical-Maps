# Maximalism (pure) ∧ Intensional Choice ⇒ ⊥

<p class='cert'>Result — Source: Misc.; produced by Cian Dorr, 16 October 2026; the consistency premise verified by Claude Opus 5.5 (Anthropic) in symmetry-constrained-full-point-and-three; recorded by Claude Opus 5.5 (Anthropic), prompted by Cian Dorr, 16 October 2026.</p>

## Premises

- **Maximalism (pure).** Every closed pure identity not provable in C is false. The non-theorem condition is metalinguistic.
- **Intensional Choice.** If a property is necessarily instantiated, then some property entailing it is necessarily uniquely instantiated.

## Conclusion

- **⊥.** These premises cannot all hold together.

## Proof

For an individual $x$ put $F_x:=\lambda y\, .\,(\exists z\, .\,z\ne x)\to y\ne x$, being distinct from $x$ if anything is; it is necessarily instantiated, by some individual other than $x$ if there is one and by $x$ otherwise. Intensional Choice at type $e$ gives, for every $x$, some $G_x\le F_x$ with $\Box\exists!y\, .\,G_xy$. Let $Q$ be the closed pure sentence $\exists x\, .\,\forall z\, .\,z=x\land \neg\exists G\, .\,G\le F_x\land\Box\exists!y\, .\,Gy$. $Q$ is consistent with C, being true at the evaluation point of symmetry-constrained-full-point-and-three (see its notes), so Maximalism (pure), in its possibility form, gives $\Diamond Q$. At a world where $Q$ holds with sole individual $a$, every actual $x$ is $a$, instantiating $\forall z\, .\,z=a$ at $x$; and $G_x\le F_x$ and $\Box\exists!y\, .\,G_xy$, which are necessary by 4, hold there too, with $F_x=F_a$. So $G_x$ is a counterexample to the second conjunct of $Q$, and $\Diamond Q$ is impossible.

## Notes

Uses Intensional Choice only at type $e$. Since Modalized Relational Choice implies Intensional Choice, it subsumes maximalism-incompatible-with-modalized-relational-choice.

## Sources

- **Dorr 16 Oct** — Cian Dorr, suggestion of 16 October 2026.
- **Opus 16 Oct** — Claude Opus 5.5 (Anthropic), prompted by Cian Dorr, 16 October 2026, for the model witnessing the consistency premise (symmetry-constrained-full-point-and-three).

<p class='cert'>Record: <code>topics/classicism/results/maximalism-incompatible-with-intensional-choice.yaml</code></p>

## Paper references

- **Background: Classicism.** Bacon, Andrew, and Cian Dorr (2024). Classicism. In Peter Fritz and Nicholas K. Jones (eds), Higher-Order Metaphysics, Oxford University Press, pp. 109–190. The map was built from the draft dated 16 May 2023, 87 pages, which does not differ materially from the published version; all page, proposition and footnote locators in this map refer to that draft's numbering. — §2.6, p. 41. Maximalist Classicism and its possibility form.
