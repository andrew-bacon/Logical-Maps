# Zorn's Lemma ⇒ Well-Ordering

<p class='cert'>Result — Source: Misc., Lean `Classicism.Map.zorn_r_implies_well_ordering_r`; produced by Claude Opus 5.5 (Anthropic), prompted by Cian Dorr, 8 October 2026, translating the standard set-theoretic argument into C; recorded by Claude Opus 5.5 (Anthropic), prompted by Cian Dorr, 8 October 2026.</p>

## Premises

- **Zorn's Lemma.** If a preorder is such that every chain, that is, every property it totally orders, has an upper bound, then something is maximal: everything above it is also below it.

## Conclusion

- **Well-Ordering.** Every type, including e, is well-ordered by some relation.

## Proof

Fix $\sigma$ and apply Zorn's Lemma at $\sigma\sigma t$. For $S^{\sigma\sigma t}$ let $\operatorname{Fld}(S):=\lambda x\, .\,(Sx)x$, and call $S$ good if $\forall x\,y\, .\,(Sx)y\to(Sx)x\land(Sy)y$ and $\operatorname{WO}(S,\operatorname{Fld}(S))$. Say $S\sqsubseteq S'$ ($S'$ end-extends $S$) if $\forall x\,y\, .\,(Sx)y\to(S'x)y$ and $\forall x\,y\, .\,(Sx)x\land(S'y)x\to(Sy)x$; this is reflexive and transitive, and if $S\sqsubseteq S'$ then $S'$ agrees with $S$ on $\operatorname{Fld}(S)$. Put $(\mathsf RS)S':=\neg\operatorname{Good}(S)\lor(\operatorname{Good}(S')\land S\sqsubseteq S')$, a preorder on $\sigma\sigma t$ in which everything not good lies below everything. Chains have upper bounds: if $\mathsf R$ totally orders $\mathcal X$, its good members are $\sqsubseteq$-comparable, and $T:=\lambda x\,y\, .\,\exists S\, .\,\mathcal XS\land\operatorname{Good}(S)\land(Sx)y$ end-extends each of them. $T$ is good: any finitely many points of $\operatorname{Fld}(T)$ lie in the field of one good member $S$, on which $T$ agrees with $S$; and if $Y\subseteq\operatorname{Fld}(T)$ has an instance in $\operatorname{Fld}(S)$, the $S$-minimal instance of $\lambda w\, .\,Yw\land(Sw)w$ is $T$-minimal in $Y$, since $(Tw)m$ with $(Sm)m$ gives $(Sw)m$. So $T$ is an $\mathsf R$-upper bound of $\mathcal X$. Zorn's Lemma gives a maximal $m$. It is good, since otherwise $(\mathsf Rm)(\lambda x\,y\, .\,\bot)$ holds and the converse fails, the empty relation being good. If some $z$ had $\neg(mz)z$, then $m':=\lambda x\,y\, .\,(mx)y\lor((mx)x\land y=z)\lor(x=z\land y=z)$, which puts $z$ on top, would be good with $m\sqsubseteq m'$; maximality gives $m'\sqsubseteq m$, so $(mz)z$, a contradiction. So $\operatorname{Fld}(m)$ is coextensive with $\lambda x\, .\,\top$, and $\operatorname{WO}(m)$, since WO depends only on extensions.

## Notes

The standard argument. End-extension of relations is only a preorder, since coextensive but distinct relations end-extend each other, which is why Zorn's Lemma is recorded for preorders. The non-good relations are placed at the bottom so that the preorder is defined on the whole type.

## Sources

- **Dorr 8 Oct** — Cian Dorr, suggestion of 8 October 2026, to connect Transversal Choice, Zorn's Lemma and Well-Ordering; proof as recorded.

<p class='cert'>Record: <code>topics/classicism/results/zorn-r-implies-well-ordering-r.yaml</code></p>
