# Extensionality ⇒ Intensional Choice

<p class='cert'>Result — Source: Misc., Lean `Classicism.Map.extensionality_r_implies_intensional_choice_r`; produced by Claude Opus 5.5 (Anthropic), 3 October 2026, from a suggestion of Cian Dorr; recorded by Claude Opus 5.5 (Anthropic), prompted by Cian Dorr, 3 October 2026.</p>

## Premises

- **Extensionality.** At each relational type, coextensive relations are identical; include the nullary propositional case.

## Conclusion

- **Intensional Choice.** If a property is necessarily instantiated, then some property entailing it is necessarily uniquely instantiated.

## Proof

Extensionality at type $t$ identifies every truth with $\top$, so $p\to\Box p$ for every proposition $p$. Let $F$ be necessarily instantiated. By T it is instantiated, say by $a$, and then $\Box Fa$. Put $G:=\lambda x\, .\,x=a$. Then $\Box\forall x\, .\,Gx\to Fx$, that is $G\le F$, and $\exists x\, .\,(Gx\land\forall y\, .\,Gy\to y=x)$ is a theorem, hence necessary.

## Notes

The witness is the haecceity of any instance.

## Sources

- **Dorr 3 Oct** — Cian Dorr, suggestion of 3 October 2026.

<p class='cert'>Record: <code>topics/classicism/results/extensionality-r-implies-intensional-choice-r.yaml</code></p>

## Paper references

- **Background: Classicism.** Bacon, Andrew, and Cian Dorr (2024). Classicism. In Peter Fritz and Nicholas K. Jones (eds), Higher-Order Metaphysics, Oxford University Press, pp. 109–190. The map was built from the draft dated 16 May 2023, 87 pages, which does not differ materially from the published version; all page, proposition and footnote locators in this map refer to that draft's numbering. — §2.1, pp. 21–23. Extensionality and its modal collapse.
