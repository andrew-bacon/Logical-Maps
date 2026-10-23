# ⊤ ⇒ Modalized Plenitude

<p class='cert'>Result — Source: Misc., Lean `Classicism.Map.classicism_implies_modalized_plenitude_r`; produced by Cian Dorr, 28 September 2026 (the principle, and the witness $\lambda x\, .\,\forall p\, .\,(Ux)p\to p$ for output type t); Claude Opus 5.5 (Anthropic), 28 September 2026, the generalization to all relational output types and the written proof; recorded by Claude Opus 5.5 (Anthropic), prompted by Cian Dorr, 28 September 2026.</p>

## Premises

- ⊤

## Conclusion

- **Modalized Plenitude.** If necessarily each argument has a value that is necessarily the relation's unique value for it, then some operation necessarily represents the relation. Its output type is relational, as required by the type system.

## Proof

Let $\tau=\bar\rho\to t$, which covers $\tau=t$ with the empty tuple, and fix $U^{\sigma\tau t}$. Write $\varphi(x,y):=(Ux)y\land\forall z\, .\,(Ux)z\to y=z$ and define the operation $F:=\lambda x^\sigma\, .\,\lambda\bar u\, .\,\forall y^\tau\, .\,(Ux)y\to y[\bar u]$; for $\tau=t$ this is $\lambda x\, .\,\forall p\, .\,(Ux)p\to p$. (1) Lemma, a theorem of C: $\varphi(x,y_0)\to\forall\bar u\, .\,y_0[\bar u]\leftrightarrow(Fx)[\bar u]$. Assume $\varphi(x,y_0)$. If $y_0[\bar u]$ and $(Ux)y$, then $y=y_0$ by uniqueness, so $y[\bar u]$; hence $(Fx)[\bar u]$. Conversely, if $(Fx)[\bar u]$, instantiate $y:=y_0$ and use $(Ux)y_0$. (2) Necessitate the lemma and apply K: $\Box\varphi(x,y_0)$ gives $\Box\forall\bar u\, .\,y_0[\bar u]\leftrightarrow(Fx)[\bar u]$, and Intensionality gives $y_0=Fx$. (3) Let $H:=\forall x\, .\,\exists y\, .\,\Box\varphi(x,y)$ and $G:=\forall x\, .\,\forall y\, .\,(Ux)y\leftrightarrow y=Fx$. Then $H\to G$ is a theorem of C. Given $x$ and $y$, take $y_0$ with $\Box\varphi(x,y_0)$; by (2) $y_0=Fx$, and by T $\varphi(x,y_0)$. If $(Ux)y$ then $y=y_0=Fx$ by uniqueness. If $y=Fx$ then $y=y_0$, and $(Ux)y_0$ gives $(Ux)y$. (4) Necessitate $H\to G$ and apply K: $\Box H\to\Box G$. Existential generalization on the closed term $F$ (with parameter $U$) gives $\Box H\to\exists X\, .\,\Box\forall x\, .\,\forall y\, .\,(Ux)y\leftrightarrow y=Xx$. Only necessitation of theorems of C is used, so the theoremhood side condition is respected.

## Notes

The operation is definable from $U$, so no choice is involved. The outer box of the hypothesis is used only to get the boxed conclusion: the same proof shows, as a theorem of C, the unboxed variant $H\to\exists X\, .\,\forall x\, .\,\forall y\, .\,(Ux)y\leftrightarrow y=Xx$. The inner box is essential; it is what licenses the identity $y_0=Fx$ in step (2). A natural target for a Lean proof, at every relational output type.

## Sources

- **Dorr 28 Sep** — Cian Dorr, 28 September 2026.
- **Classicism** — Andrew Bacon and Cian Dorr, Classicism, draft of 16 May 2023, §1.5, pp. 16–18 (necessitation, T and Intensionality).

<p class='cert'>Record: <code>topics/classicism/results/classicism-implies-modalized-plenitude-r.yaml</code></p>

## Paper references

- **Background: Classicism.** Bacon, Andrew, and Cian Dorr (2024). Classicism. In Peter Fritz and Nicholas K. Jones (eds), Higher-Order Metaphysics, Oxford University Press, pp. 109–190. The map was built from the draft dated 16 May 2023, 87 pages, which does not differ materially from the published version; all page, proposition and footnote locators in this map refer to that draft's numbering. — §1.5, pp. 16–18. Necessitation, T and Intensionality (necessarily coextensive relations are identical).
