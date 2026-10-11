# Modal Well-Ordering ⇒ Intensional Choice

<p class='cert'>Result — Source: Misc., Lean `Classicism.Map.modal_well_ordering_r_implies_intensional_choice_r`; produced by Claude Opus 5.5 (Anthropic), 7 October 2026, in an argument sketched by Cian Dorr; recorded by Claude Opus 5.5 (Anthropic), 8 October 2026.</p>

## Premises

- **Modal Well-Ordering.** Every type, including e, has a relation that is necessarily a well-order of it.

## Conclusion

- **Intensional Choice.** If a property is necessarily instantiated, then some property entailing it is necessarily uniquely instantiated.

## Proof

Let $\Box\operatorname{WO}(R)$, and let $F$ be necessarily instantiated. Put $G:=\lambda x\, .\,Fx\land\forall y\, .\,Fy\to(Rx)y$, so that $G\le F$. At any world, $F$ is instantiated and $R$ is a well-order, so $F$ has an $R$-minimal instance $x$. For any instance $y$ of $F$, Total gives $(Rx)y$ or $(Ry)x$, and in the second case minimality gives $y=x$, whence $(Rx)y$ by Total again; so $Gx$. If also $Gy$, then $(Rx)y$ and $(Ry)x$, and Antisymm gives $y=x$. Hence $\Box\exists x\, .\,Gx\land\forall y\, .\,Gy\to y=x$.

## Notes

The selected property is the least instance of $F$ in the necessary well-order, which may be a different individual at different worlds.

## Sources

- **Dorr 7 Oct** — Cian Dorr, suggestion of 7 October 2026, in conversation with Claude Opus 5.5 (Anthropic).

<p class='cert'>Record: <code>topics/classicism/results/modal-well-ordering-r-implies-intensional-choice-r.yaml</code></p>
