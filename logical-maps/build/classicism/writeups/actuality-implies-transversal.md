# Actuality ⇒ Transversal

<p class='cert'>Result — Source: Misc., Lean `Classicism.Map.actuality_implies_transversal`; produced by Christopher Sun (the claim and the witness), 26 September 2026; recorded by Claude Opus 5.5 (Anthropic), prompted by Cian Dorr, 28 September 2026.</p>

## Premises

- **Actuality.** There is a true proposition that entails every true proposition.

## Conclusion

- **Transversal.** There is a property of properties that picks out exactly one property from each coextension class, that is, exactly one property coextensive with any given property.

## Proof

Let $w$ witness Actuality: $w$ is true and $w\le q$ for every true $q$. Fix $\sigma$ and put $FY:=\Box\forall z^\sigma\, .\,Yz\to w$, the property of being a property that can be instantiated only if $w$ obtains. Existence: given $X$, let $Y:=\lambda z\, .\,Xz\land w$. Since $w$ is true, $Y$ is coextensive with $X$, and $FY$ holds because $\forall z\, .\,(Xz\land w)\to w$ is a theorem, hence necessary. Uniqueness: let $Y_1$ and $Y_2$ satisfy $F$ and be coextensive with $X$. Then $Y_1\equiv Y_2$ is true, so Actuality gives $\Box(w\toY_1\equiv Y_2)$. Together with $\Box\forall z\, .\,Y_1z\to w$ and $\Box\forall z\, .\,Y_2z\to w$, K gives $\Box(Y_1\equiv Y_2)$: at any $z$, if either side holds then $w$ does, and then the two sides agree. Necessarily coextensive properties are identical in C (Intensionality), so $Y_1=Y_2$.

## Notes

Two coextensive $F$-properties are necessarily coextensive. The dual witness $FY:=\Box\forall z\, .\,w\lor Yz$, with representative $\lambda z\, .\,Xz\lor\neg w$, works equally well. With Transversal and Relational Choice implying Transversal Choice, Actuality and Relational Choice together imply Transversal Choice.

## Sources

- **Sun 26 Sep** — Christopher Sun, 26 September 2026.
- **Classicism** — Andrew Bacon and Cian Dorr, Classicism, draft of 16 May 2023, §1.5, p. 16 (Intensionality).

<p class='cert'>Record: <code>topics/classicism/results/actuality-implies-transversal.yaml</code></p>

## Paper references

- **Background: Classicism.** Bacon, Andrew, and Cian Dorr (2024). Classicism. In Peter Fritz and Nicholas K. Jones (eds), Higher-Order Metaphysics, Oxford University Press, pp. 109–190. The map was built from the draft dated 16 May 2023, 87 pages, which does not differ materially from the published version; all page, proposition and footnote locators in this map refer to that draft's numbering. — §1.5, p. 16. Intensionality, the identity of necessarily coextensive relations.
