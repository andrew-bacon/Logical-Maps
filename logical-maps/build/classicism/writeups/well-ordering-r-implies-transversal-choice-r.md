# Well-Ordering ⇒ Transversal Choice

<p class='cert'>Result — Source: Misc., Lean `Classicism.Map.well_ordering_r_implies_transversal_choice_r`; produced by Claude Opus 5.5 (Anthropic), 8 October 2026; recorded by Claude Opus 5.5 (Anthropic), 8 October 2026.</p>

## Premises

- **Well-Ordering.** Every type, including e, is well-ordered by some relation.

## Conclusion

- **Transversal Choice.** Every equivalence relation, at any type including e, has a transversal, that is, a property with exactly one instance in each of its cells.

## Proof

Let $\operatorname{WO}(R)$ at $\sigma$, write $x\preccurlyeq y$ for $(Rx)y$, and let $E$ be an equivalence relation on $\sigma$. Put $Fy:=\forall z\, .\,(Ey)z\to y\preccurlyeq z$. Given $x$, the cell $\lambda z\, .\,(Ex)z$ is instantiated by $x$, so it has an $R$-minimal instance $m$, which is its least instance: for $z$ in the cell, Total gives $m\preccurlyeq z$ or $z\preccurlyeq m$, and in the second case minimality gives $z=m$. Since $(Em)z$ implies $(Ex)z$, $Fm$ holds, and $(Ex)m$. If also $(Ex)z$ and $Fz$, then $(Em)z$ and $(Ez)m$, so $m\preccurlyeq z$ and $z\preccurlyeq m$, and Antisymm gives $z=m$.

## Notes

Each cell's chosen instance is its least element in the well-order. Well-Ordering is used only at $\sigma$.

## Sources

- **Dorr 8 Oct** — Cian Dorr, suggestion of 8 October 2026, to connect Transversal Choice, Zorn's Lemma and Well-Ordering; proof as recorded.

<p class='cert'>Record: <code>topics/classicism/results/well-ordering-r-implies-transversal-choice-r.yaml</code></p>
