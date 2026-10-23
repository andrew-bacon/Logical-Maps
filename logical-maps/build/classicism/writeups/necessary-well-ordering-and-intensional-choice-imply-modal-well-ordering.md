# □Well-Ordering ∧ Intensional Choice ⇒ Modal Well-Ordering

<p class='cert'>Result — Source: Misc., Lean `Classicism.Map.necessary_well_ordering_and_intensional_choice_imply_modal_well_ordering`; produced by Cian Dorr, 8 October 2026; recorded by Claude Opus 5.5 (Anthropic), prompted by Cian Dorr, 8 October 2026.</p>

## Premises

- **□Well-Ordering.** Necessarily, every type, including e, is well-ordered by some relation.
- **Intensional Choice.** If a property is necessarily instantiated, then some property entailing it is necessarily uniquely instantiated.

## Conclusion

- **Modal Well-Ordering.** Every type, including e, has a relation that is necessarily a well-order of it.

## Proof

Apply Intensional Choice at the type $\sigma\sigma t$ to $F:=\lambda R\, .\,\operatorname{WO}(R)$, which is necessarily instantiated by $\Box$Well-Ordering. This gives $G\le F$ that is necessarily uniquely instantiated. Put $R':=\lambda x\,y\, .\,\exists R\, .\,GR\land(Rx)y$. At any world the unique instance $R_0$ of $G$ there is a well-order, since $G\le F$, and $R'$ is coextensive with $R_0$ there. WO depends only on the extension of its argument at the evaluation point (Background), so $\operatorname{WO}(R')$ holds there. Hence $\Box\operatorname{WO}(R')$.

## Notes

Intensional Choice is used at the type $\sigma\sigma t$ to obtain Modal Well-Ordering at $\sigma$.

## Sources

- **Dorr 8 Oct** — Cian Dorr, 8 October 2026.

<p class='cert'>Record: <code>topics/classicism/results/necessary-well-ordering-and-intensional-choice-imply-modal-well-ordering.yaml</code></p>
